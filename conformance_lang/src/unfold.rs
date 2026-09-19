//! Unfold — one Observe backend. Walk `self` / `m` rewrite; path-split;
//! follow Known callee writes. Not the camera: layout and live Observe
//! never enter here.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{
    parse_str, Attribute, BinOp, Block, Expr, ExprLit, FnArg, ImplItem, Item, ItemImpl, Lit,
    Member, Pat, Stmt, Token, Type,
};

use crate::absval::AbsVal;
use crate::ir::{Schema, ValueCtx};
use crate::observe::Fact;
use crate::{eval_rewrites, eval_schema, CheckReport, Skip};

const FOLLOW_DEPTH: usize = 8;

/// One path's snapshot of the schema value.
#[derive(Debug, Clone)]
pub struct Observation {
    pub label: String,
    pub ctx: ValueCtx,
    pub rewrites: CheckReport,
}

struct FnDef {
    name: String,
    subject: String,
    params: Vec<String>,
    is_tuple: bool,
    block: Block,
    except: Option<String>,
}

struct Path {
    label: String,
    ctx: ValueCtx,
    done: bool,
    rewrites: CheckReport,
}

impl Path {
    fn at(ctx: ValueCtx, label: String, done: bool) -> Self {
        Path {
            ctx,
            label,
            done,
            rewrites: CheckReport::default(),
        }
    }
}

struct Engine<'a> {
    schema: &'a Schema,
    fns: &'a BTreeMap<String, Vec<FnDef>>,
    subject: &'a str,
    depth: usize,
}

/// Parse `source`, observe every fn that rewrites a value of `schema`'s type.
/// `#[except("…")]` sites are omitted here (still in the follow map).
pub fn unfold(schema: &Schema, source: &str) -> Result<Vec<Observation>, String> {
    Ok(unfold_ex(schema, source)?.0)
}

fn unfold_ex(schema: &Schema, source: &str) -> Result<(Vec<Observation>, Vec<Skip>), String> {
    let file: syn::File = parse_str(source).map_err(|e| e.to_string())?;
    let fns = collect_fns(&file, schema);
    let mut skipped = Vec::new();
    let mut out = Vec::new();
    for def in fns.values().flatten() {
        if !def.is_tuple {
            continue;
        }
        if let Some(reason) = &def.except {
            skipped.push(Skip {
                site: def.name.clone(),
                reason: reason.clone(),
            });
            continue;
        }
        let engine = Engine {
            schema,
            fns: &fns,
            subject: &def.subject,
            depth: 0,
        };
        out.extend(engine.run(def));
    }
    Ok((out, skipped))
}

pub fn eval_unfold(schema: &Schema, source: &str) -> Result<CheckReport, String> {
    let (obs, skipped) = unfold_ex(schema, source)?;
    let mut report = CheckReport {
        skipped,
        ..CheckReport::default()
    };
    for ob in obs {
        report.merge(ob.rewrites);
        report
            .findings
            .extend(eval_schema(schema, &ob.ctx, Some(&ob.label)).findings);
    }
    Ok(report)
}

/// Unfold `source`, eval only paths that belong to `name` (and its `then`/`else` crumbs).
/// Callees followed from that fn are included; other top-level fns are not.
pub fn eval_unfold_named(schema: &Schema, source: &str, name: &str) -> Result<CheckReport, String> {
    let (obs, skipped) = unfold_ex(schema, source)?;
    if let Some(s) = skipped.iter().find(|s| s.site == name) {
        return Ok(CheckReport {
            skipped: vec![s.clone()],
            ..CheckReport::default()
        });
    }
    let mut report = CheckReport::default();
    let prefix = format!("{name}.");
    let mut any = false;
    for ob in obs {
        if ob.label == name || ob.label.starts_with(&prefix) {
            any = true;
            report.merge(ob.rewrites);
            report
                .findings
                .extend(eval_schema(schema, &ob.ctx, Some(&ob.label)).findings);
        }
    }
    if !any {
        return Err(format!(
            "no unfold paths for `{name}` (need a param/receiver of type {})",
            schema.name
        ));
    }
    Ok(report)
}

/// Driver: Unfold every `.rs` under `{manifest_dir}/src` at expand time.
/// Schema is the default site opt-in. Same backend as `eval_unfold` — not a new camera.
pub fn eval_crate(
    schema: &Schema,
    manifest_dir: impl AsRef<FsPath>,
) -> Result<CheckReport, String> {
    eval_tree(schema, &manifest_dir.as_ref().join("src"))
}

pub fn eval_tree(schema: &Schema, dir: &FsPath) -> Result<CheckReport, String> {
    let mut report = CheckReport::default();
    if !dir.exists() {
        return Ok(report);
    }
    for path in rust_files(dir)? {
        let src = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut one = eval_unfold(schema, &src)?;
        let file = path.display().to_string();
        for f in &mut one.findings {
            f.site = Some(match &f.site {
                Some(site) => format!("{file}::{site}"),
                None => file.clone(),
            });
        }
        for s in &mut one.skipped {
            s.site = format!("{file}::{}", s.site);
        }
        report.merge(one);
    }
    Ok(report)
}

fn rust_files(dir: &FsPath) -> Result<Vec<PathBuf>, String> {
    let mut out = Vec::new();
    rust_files_into(dir, &mut out)?;
    out.sort();
    Ok(out)
}

fn rust_files_into(dir: &FsPath, out: &mut Vec<PathBuf>) -> Result<(), String> {
    for ent in fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let ent = ent.map_err(|e| e.to_string())?;
        let p = ent.path();
        if p.is_dir() {
            rust_files_into(&p, out)?;
        } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(p);
        }
    }
    Ok(())
}

fn collect_fns(file: &syn::File, schema: &Schema) -> BTreeMap<String, Vec<FnDef>> {
    let mut fns: BTreeMap<String, Vec<FnDef>> = BTreeMap::new();
    for item in &file.items {
        match item {
            Item::Fn(f) => {
                let def = fn_from_parts(
                    f.sig.ident.to_string(),
                    &f.sig.inputs,
                    &f.block,
                    &f.attrs,
                    None,
                    schema,
                );
                fns.entry(def.name.clone()).or_default().push(def);
            }
            Item::Impl(im) => collect_impl(&mut fns, im, schema),
            _ => {}
        }
    }
    fns
}

fn collect_impl(fns: &mut BTreeMap<String, Vec<FnDef>>, im: &ItemImpl, schema: &Schema) {
    let impl_ty = type_last_ident(&im.self_ty);
    for item in &im.items {
        let ImplItem::Fn(m) = item else { continue };
        let def = fn_from_parts(
            m.sig.ident.to_string(),
            &m.sig.inputs,
            &m.block,
            &m.attrs,
            impl_ty.as_deref(),
            schema,
        );
        fns.entry(def.name.clone()).or_default().push(def);
    }
}

fn fn_from_parts(
    name: String,
    inputs: &Punctuated<FnArg, Token![,]>,
    block: &Block,
    attrs: &[Attribute],
    impl_ty: Option<&str>,
    schema: &Schema,
) -> FnDef {
    let except = except_reason(attrs);
    let mut subject = String::new();
    let mut params = Vec::new();
    let mut is_tuple = false;
    for input in inputs {
        match input {
            FnArg::Receiver(_) => {
                subject = "self".into();
                if impl_ty == Some(schema.name.as_str()) {
                    is_tuple = true;
                }
            }
            FnArg::Typed(pat) => {
                let Pat::Ident(id) = &*pat.pat else { continue };
                let pname = id.ident.to_string();
                if type_last_ident(&pat.ty).as_deref() == Some(schema.name.as_str()) {
                    is_tuple = true;
                    subject = pname;
                } else {
                    if subject.is_empty() {
                        subject = pname.clone();
                    }
                    params.push(pname);
                }
            }
        }
    }
    FnDef {
        name,
        subject,
        params,
        is_tuple,
        block: block.clone(),
        except,
    }
}

fn find_tuple<'a>(fns: &'a BTreeMap<String, Vec<FnDef>>, name: &str) -> Option<&'a FnDef> {
    fns.get(name)?.iter().find(|d| d.is_tuple)
}

fn find_slot<'a>(fns: &'a BTreeMap<String, Vec<FnDef>>, name: &str) -> Option<&'a FnDef> {
    fns.get(name)?.iter().find(|d| !d.is_tuple)
}

fn except_reason(attrs: &[Attribute]) -> Option<String> {
    for attr in attrs {
        if attr
            .path()
            .segments
            .last()
            .is_none_or(|s| s.ident != "except")
        {
            continue;
        }
        if let Ok(s) = attr.parse_args::<syn::LitStr>() {
            let v = s.value();
            if !v.trim().is_empty() {
                return Some(v);
            }
        }
    }
    None
}

fn type_last_ident(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        Type::Reference(r) => type_last_ident(&r.elem),
        Type::Paren(p) => type_last_ident(&p.elem),
        _ => None,
    }
}

impl Engine<'_> {
    fn run(&self, def: &FnDef) -> Vec<Observation> {
        self.exec_block(&def.block, ValueCtx::default(), def.name.clone())
            .into_iter()
            .map(|p| Observation {
                label: p.label,
                ctx: p.ctx,
                rewrites: p.rewrites,
            })
            .collect()
    }

    fn exec_block(&self, block: &Block, ctx: ValueCtx, label: String) -> Vec<Path> {
        self.exec_seq(&block.stmts, ctx, label)
    }

    fn exec_seq(&self, stmts: &[Stmt], ctx: ValueCtx, label: String) -> Vec<Path> {
        let Some((head, tail)) = stmts.split_first() else {
            return vec![Path::at(ctx, label, false)];
        };
        let continue_with = |paths: Vec<Path>| -> Vec<Path> {
            paths
                .into_iter()
                .flat_map(|p| {
                    if p.done || tail.is_empty() {
                        vec![p]
                    } else {
                        let prior = p.rewrites;
                        self.exec_seq(tail, p.ctx, p.label)
                            .into_iter()
                            .map(|mut kid| {
                                let mut rewrites = prior.clone();
                                rewrites.merge(std::mem::take(&mut kid.rewrites));
                                kid.rewrites = rewrites;
                                kid
                            })
                            .collect()
                    }
                })
                .collect()
        };

        match head {
            Stmt::Expr(expr, semi) => {
                let as_return = tail.is_empty() && semi.is_none();
                continue_with(self.exec_expr(expr, ctx, label, as_return))
            }
            Stmt::Local(local) => {
                let p = self.exec_local(local, ctx, label);
                continue_with(vec![p])
            }
            _ => continue_with(vec![Path::at(ctx, label, false)]),
        }
    }

    fn exec_local(&self, local: &syn::Local, ctx: ValueCtx, label: String) -> Path {
        let Some(init) = &local.init else {
            return Path::at(ctx, label, false);
        };
        let Pat::Ident(id) = &local.pat else {
            return Path::at(ctx, label, false);
        };
        if id.ident != self.subject {
            return Path::at(ctx, label, false);
        }
        let mut p = self
            .apply_value(&init.expr, ctx)
            .into_iter()
            .next()
            .expect("apply_value yields a path");
        p.label = label;
        p.done = false;
        p
    }

    fn exec_if(&self, i: &syn::ExprIf, ctx: ValueCtx, label: String, as_return: bool) -> Vec<Path> {
        let (thens, elses) = self.cond_paths(&i.cond, ctx, &label);
        let mut then_ps: Vec<Path> = thens
            .into_iter()
            .flat_map(|(c, l)| self.exec_block(&i.then_branch, c, l))
            .collect();
        let mut else_ps: Vec<Path> = match &i.else_branch {
            Some((_, e)) => elses
                .into_iter()
                .flat_map(|(c, l)| self.exec_expr(e, c, l, as_return))
                .collect(),
            None => elses
                .into_iter()
                .map(|(ctx, label)| Path::at(ctx, label, false))
                .collect(),
        };
        if as_return {
            for p in then_ps.iter_mut().chain(else_ps.iter_mut()) {
                p.done = true;
            }
        }
        then_ps.into_iter().chain(else_ps).collect()
    }

    fn exec_expr(&self, expr: &Expr, ctx: ValueCtx, label: String, as_return: bool) -> Vec<Path> {
        match expr {
            Expr::If(i) => self.exec_if(i, ctx, label, as_return),
            Expr::Block(b) => {
                let mut ps = self.exec_block(&b.block, ctx, label);
                if as_return {
                    for p in &mut ps {
                        p.done = true;
                    }
                }
                ps
            }
            Expr::Return(r) => match &r.expr {
                Some(e) => self
                    .apply_value(e, ctx)
                    .into_iter()
                    .map(|mut p| {
                        p.label = label.clone();
                        p.done = true;
                        p
                    })
                    .collect(),
                None => vec![Path::at(ctx, label, true)],
            },
            Expr::Assign(a) => {
                let mut ps = self.exec_assign(a, ctx, label);
                if as_return {
                    for p in &mut ps {
                        p.done = true;
                    }
                }
                ps
            }
            _ => {
                let mut ps = self.apply_value(expr, ctx);
                for p in &mut ps {
                    p.label = label.clone();
                    if as_return {
                        p.done = true;
                    }
                }
                ps
            }
        }
    }

    fn exec_assign(&self, a: &syn::ExprAssign, ctx: ValueCtx, label: String) -> Vec<Path> {
        if let Expr::Field(f) = &*a.left {
            if is_subject(&f.base, self.subject) {
                let name = member_name(&f.member);
                if self.has_field(&name) {
                    return self
                        .observe_write(&name, &a.right, ctx)
                        .into_iter()
                        .map(|(pre, write)| {
                            let rewrites =
                                eval_rewrites(self.schema, &pre, &name, &write, Some(&label));
                            Path {
                                ctx: pre.put(&name, write),
                                label: label.clone(),
                                done: false,
                                rewrites,
                            }
                        })
                        .collect();
                }
            }
        }
        if is_subject(&a.left, self.subject) {
            return self
                .apply_value(&a.right, ctx)
                .into_iter()
                .map(|mut p| {
                    p.label = label.clone();
                    p.done = false;
                    p
                })
                .collect();
        }
        vec![Path::at(ctx, label, false)]
    }

    fn apply_value(&self, expr: &Expr, ctx: ValueCtx) -> Vec<Path> {
        let expr = peel(expr);
        if is_default(expr) {
            return vec![Path::at(self.unknown_all(ctx), String::new(), false)];
        }
        if let Expr::Struct(s) = expr {
            return vec![Path::at(self.apply_struct(s, ctx), String::new(), false)];
        }
        if let Some(ps) = self.try_follow(expr, ctx.clone()) {
            return ps
                .into_iter()
                .map(|mut p| {
                    p.done = false;
                    p
                })
                .collect();
        }
        vec![Path::at(ctx, String::new(), false)]
    }

    /// A write is Observe of the RHS at this field (slot follow).
    fn observe_write(&self, field: &str, expr: &Expr, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        Slot {
            schema: self.schema,
            fns: self.fns,
            field,
            binds: BTreeMap::new(),
            tuple_subject: Some(self.subject),
            depth: self.depth,
        }
        .observe(expr, ctx)
    }

    fn try_follow(&self, expr: &Expr, ctx: ValueCtx) -> Option<Vec<Path>> {
        if self.depth >= FOLLOW_DEPTH {
            return None;
        }
        let name = called_name(expr)?;
        let def = find_tuple(self.fns, &name)?;
        if !call_touches_subject(expr, self.subject) {
            return None;
        }
        let inner = Engine {
            schema: self.schema,
            fns: self.fns,
            subject: &def.subject,
            depth: self.depth + 1,
        };
        Some(inner.exec_block(&def.block, ctx, def.name.clone()))
    }

    fn cond_paths(&self, cond: &Expr, ctx: ValueCtx, label: &str) -> CondSplit {
        match parse_cond(cond, Some(self.subject), &BTreeMap::new()) {
            Some(c) if self.cond_known(&c) => self.split_cond(&c, ctx, label),
            _ => (
                vec![(ctx.clone(), format!("{label}.then"))],
                vec![(ctx, format!("{label}.else"))],
            ),
        }
    }

    fn cond_known(&self, cond: &Cond) -> bool {
        match cond {
            Cond::Eq { field, .. } | Cond::In { field, .. } => self.has_field(field),
            Cond::And(a, b) | Cond::Or(a, b) => self.cond_known(a) && self.cond_known(b),
        }
    }

    fn split_cond(&self, cond: &Cond, ctx: ValueCtx, label: &str) -> CondSplit {
        split_cond(cond, ctx, label)
    }

    fn apply_struct(&self, s: &syn::ExprStruct, mut ctx: ValueCtx) -> ValueCtx {
        let Some(seg) = s.path.segments.last() else {
            return ctx;
        };
        if seg.ident != self.schema.name {
            return ctx;
        }
        for field in &s.fields {
            let Member::Named(id) = &field.member else {
                continue;
            };
            let name = id.to_string();
            if self.has_field(&name) {
                ctx = ctx.put(&name, fact_of(&field.expr));
            }
        }
        ctx
    }

    fn unknown_all(&self, ctx: ValueCtx) -> ValueCtx {
        self.schema
            .fields
            .iter()
            .fold(ctx, |c, f| c.unknown(&f.name))
    }

    fn has_field(&self, name: &str) -> bool {
        self.schema.fields.iter().any(|f| f.name == name)
    }
}

/// Observe one field's RHS: peel, bind params to Schema fields, split matches.
struct Slot<'a> {
    schema: &'a Schema,
    fns: &'a BTreeMap<String, Vec<FnDef>>,
    field: &'a str,
    binds: BTreeMap<String, String>,
    tuple_subject: Option<&'a str>,
    depth: usize,
}

impl Slot<'_> {
    fn observe(&self, expr: &Expr, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        let expr = peel(expr);
        if let Some((_, ident, body)) = as_map_closure(expr) {
            let mut binds = self.binds.clone();
            binds.insert(ident, self.field.to_string());
            return Slot {
                schema: self.schema,
                fns: self.fns,
                field: self.field,
                binds,
                tuple_subject: self.tuple_subject,
                depth: self.depth,
            }
            .observe(body, ctx);
        }
        if let Some(inner) = unwrap_ctor(expr) {
            return self.observe(inner, ctx);
        }
        match expr {
            Expr::Match(m) => self.observe_match(m, ctx),
            Expr::If(i) => self.observe_if(i, ctx),
            Expr::Return(r) => match &r.expr {
                Some(e) => self.observe(e, ctx),
                None => vec![(ctx, Fact::Unknown)],
            },
            Expr::Block(b) => self.observe_block(&b.block, ctx),
            _ => {
                if let Some(ps) = self.follow(expr, ctx.clone()) {
                    return ps;
                }
                if let Some(f) = resolve_field(expr, self.tuple_subject, &self.binds) {
                    return vec![(ctx.clone(), fact_of_ctx(&ctx, &f))];
                }
                vec![(ctx, fact_of(expr))]
            }
        }
    }

    fn observe_block(&self, block: &Block, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        self.observe_stmts(&block.stmts, ctx)
    }

    fn observe_stmts(&self, stmts: &[Stmt], ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        if let Some((i, rest)) = leading_if_return(stmts) {
            let (thens, elses) = self.cond_split(&i.cond, ctx);
            let mut out = Vec::new();
            for (c, _) in thens {
                out.extend(self.observe_block(&i.then_branch, c));
            }
            for (c, _) in elses {
                out.extend(self.observe_stmts(rest, c));
            }
            return out;
        }
        match stmts {
            [] => vec![(ctx, Fact::Unknown)],
            [only] => self.observe_stmt(only, ctx),
            [Stmt::Local(_), tail @ ..] => self.observe_stmts(tail, ctx),
            [head, ..] => self.observe_stmt(head, ctx),
        }
    }

    fn observe_stmt(&self, stmt: &Stmt, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        match stmt {
            Stmt::Expr(e, _) => self.observe(e, ctx),
            _ => vec![(ctx, Fact::Unknown)],
        }
    }

    fn observe_if(&self, i: &syn::ExprIf, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        let (thens, elses) = self.cond_split(&i.cond, ctx);
        let mut out = Vec::new();
        for (c, _) in thens {
            out.extend(self.observe_block(&i.then_branch, c));
        }
        match &i.else_branch {
            Some((_, e)) => {
                for (c, _) in elses {
                    out.extend(self.observe(e, c));
                }
            }
            None => {
                for (c, _) in elses {
                    out.push((c, Fact::Unknown));
                }
            }
        }
        out
    }

    fn observe_match(&self, m: &syn::ExprMatch, ctx: ValueCtx) -> Vec<(ValueCtx, Fact)> {
        let field = resolve_field(&m.expr, self.tuple_subject, &self.binds)
            .unwrap_or_else(|| self.field.to_string());
        let covered: Vec<String> = m
            .arms
            .iter()
            .filter_map(|a| pat_str_lits(&a.pat))
            .flatten()
            .collect();
        let mut out = Vec::new();
        for arm in &m.arms {
            if pat_is_multiple(&arm.pat) {
                out.push((ctx.clone(), Fact::Unknown));
                continue;
            }
            if let Some(lits) = pat_str_lits(&arm.pat) {
                for lit in lits {
                    let c = ctx.clone().lit(&field, lit);
                    out.extend(self.observe(&arm.body, c));
                }
                continue;
            }
            if let Some(id) = pat_ident(&arm.pat) {
                let mut binds = self.binds.clone();
                binds.insert(id, field.clone());
                let pre = covered
                    .iter()
                    .fold(ctx.clone(), |c, l| c.exclude(&field, l));
                out.extend(
                    Slot {
                        schema: self.schema,
                        fns: self.fns,
                        field: self.field,
                        binds,
                        tuple_subject: self.tuple_subject,
                        depth: self.depth,
                    }
                    .observe(&arm.body, pre),
                );
                continue;
            }
            out.push((ctx.clone(), Fact::Unknown));
        }
        if out.is_empty() {
            out.push((ctx, Fact::Unknown));
        }
        out
    }

    fn cond_split(&self, cond: &Expr, ctx: ValueCtx) -> CondSplit {
        match parse_cond(cond, self.tuple_subject, &self.binds) {
            Some(c) if cond_fields_known(&c, self.schema) => split_cond(&c, ctx, "slot"),
            _ => (
                vec![(ctx.clone(), "then".into())],
                vec![(ctx, "else".into())],
            ),
        }
    }

    fn follow(&self, expr: &Expr, ctx: ValueCtx) -> Option<Vec<(ValueCtx, Fact)>> {
        if self.depth >= FOLLOW_DEPTH {
            return None;
        }
        let name = called_name(expr)?;
        let def = find_slot(self.fns, &name)?;
        let binds = bind_call(def, expr, self);
        Some(
            Slot {
                schema: self.schema,
                fns: self.fns,
                field: self.field,
                binds,
                tuple_subject: None,
                depth: self.depth + 1,
            }
            .observe_block(&def.block, ctx),
        )
    }
}

fn bind_call(def: &FnDef, expr: &Expr, slot: &Slot<'_>) -> BTreeMap<String, String> {
    let mut binds = BTreeMap::new();
    match peel(expr) {
        Expr::MethodCall(m) => {
            binds.insert(def.subject.clone(), slot.field.to_string());
            for (p, a) in def.params.iter().zip(&m.args) {
                if let Some(f) = resolve_field(a, slot.tuple_subject, &slot.binds) {
                    binds.insert(p.clone(), f);
                }
            }
        }
        Expr::Call(c) => {
            for (p, a) in def.params.iter().zip(&c.args) {
                if let Some(f) = resolve_field(a, slot.tuple_subject, &slot.binds) {
                    binds.insert(p.clone(), f);
                }
            }
        }
        _ => {}
    }
    binds
}

fn as_map_closure(expr: &Expr) -> Option<(&Expr, String, &Expr)> {
    let Expr::MethodCall(m) = peel(expr) else {
        return None;
    };
    if m.method != "map" {
        return None;
    }
    let Expr::Closure(c) = peel(m.args.first()?) else {
        return None;
    };
    let Pat::Ident(id) = c.inputs.first()? else {
        return None;
    };
    Some((&m.receiver, id.ident.to_string(), &c.body))
}

fn unwrap_ctor(expr: &Expr) -> Option<&Expr> {
    let Expr::Call(c) = peel(expr) else {
        return None;
    };
    match path_last(&c.func).as_deref() {
        Some("Some") | Some("Single") => c.args.first(),
        _ => None,
    }
}

fn leading_if_return(stmts: &[Stmt]) -> Option<(&syn::ExprIf, &[Stmt])> {
    let (head, rest) = stmts.split_first()?;
    let Stmt::Expr(expr, _) = head else {
        return None;
    };
    let Expr::If(i) = peel(expr) else {
        return None;
    };
    if i.else_branch.is_some() {
        return None;
    }
    if !block_returns(&i.then_branch) {
        return None;
    }
    Some((i, rest))
}

fn block_returns(block: &Block) -> bool {
    block.stmts.iter().any(|s| {
        let Stmt::Expr(e, _) = s else {
            return false;
        };
        matches!(peel(e), Expr::Return(_))
    })
}

fn pat_is_multiple(pat: &Pat) -> bool {
    match pat {
        Pat::TupleStruct(t) => t
            .path
            .segments
            .last()
            .is_some_and(|s| s.ident == "Multiple"),
        _ => false,
    }
}

fn pat_ident(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(id) => Some(id.ident.to_string()),
        Pat::Reference(r) => pat_ident(&r.pat),
        Pat::TupleStruct(t) => {
            let last = t.path.segments.last()?.ident.to_string();
            if last != "Some" && last != "Single" {
                return None;
            }
            pat_ident(t.elems.first()?)
        }
        _ => None,
    }
}

fn fact_of_ctx(ctx: &ValueCtx, field: &str) -> Fact {
    match ctx.values.get(field) {
        Some(AbsVal::Known(s)) => Fact::Lit(s.clone()),
        Some(AbsVal::Absent) => Fact::Absent,
        Some(AbsVal::OneOf(vs)) => Fact::OneOf(vs.iter().cloned().collect()),
        Some(AbsVal::Array(xs)) => Fact::Array(xs.iter().cloned().map(abs_fact).collect()),
        Some(AbsVal::Record(m)) => {
            Fact::Record(m.iter().map(|(k, v)| (k.clone(), abs_fact(v.clone()))).collect())
        }
        Some(AbsVal::Unknown) | None => Fact::Unknown,
    }
}

fn abs_fact(val: AbsVal) -> Fact {
    match val {
        AbsVal::Known(s) => Fact::Lit(s),
        AbsVal::Absent => Fact::Absent,
        AbsVal::Unknown => Fact::Unknown,
        AbsVal::OneOf(vs) => Fact::OneOf(vs.into_iter().collect()),
        AbsVal::Array(xs) => Fact::Array(xs.into_iter().map(abs_fact).collect()),
        AbsVal::Record(m) => {
            Fact::Record(m.into_iter().map(|(k, v)| (k, abs_fact(v))).collect())
        }
    }
}

fn cond_fields_known(cond: &Cond, schema: &Schema) -> bool {
    match cond {
        Cond::Eq { field, .. } | Cond::In { field, .. } => {
            schema.fields.iter().any(|f| f.name == *field)
        }
        Cond::And(a, b) | Cond::Or(a, b) => {
            cond_fields_known(a, schema) && cond_fields_known(b, schema)
        }
    }
}

fn split_cond(cond: &Cond, ctx: ValueCtx, label: &str) -> CondSplit {
    match cond {
        Cond::Eq { field, lit } => (
            vec![(
                ctx.clone().lit(field, lit.clone()),
                format!("{label}.then[{field}=={lit}]"),
            )],
            vec![(
                ctx.exclude(field, lit),
                format!("{label}.else[{field}=={lit}]"),
            )],
        ),
        Cond::In { field, lits } => (
            vec![(
                ctx.clone().one_of(field, lits.clone()),
                format!("{label}.then[{field} in {lits:?}]"),
            )],
            vec![(
                lits.iter().fold(ctx, |c, l| c.exclude(field, l)),
                format!("{label}.else[{field} in {lits:?}]"),
            )],
        ),
        Cond::And(left, right) => {
            let (l_then, l_else) = split_cond(left, ctx, label);
            let mut thens = Vec::new();
            let mut elses = l_else;
            for (c, l) in l_then {
                let (r_then, r_else) = split_cond(right, c, &l);
                thens.extend(r_then);
                elses.extend(r_else);
            }
            (thens, elses)
        }
        Cond::Or(left, right) => {
            let (l_then, l_else) = split_cond(left, ctx, label);
            let mut thens = l_then;
            let mut elses = Vec::new();
            for (c, l) in l_else {
                let (r_then, r_else) = split_cond(right, c, &l);
                thens.extend(r_then);
                elses.extend(r_else);
            }
            (thens, elses)
        }
    }
}

fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(p) => peel(&p.expr),
        Expr::Reference(r) => peel(&r.expr),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => peel(&u.expr),
        Expr::MethodCall(m)
            if matches!(
                m.method.to_string().as_str(),
                "into"
                    | "to_string"
                    | "to_owned"
                    | "clone"
                    | "as_deref"
                    | "as_str"
                    | "as_ref"
                    | "take"
            ) =>
        {
            peel(&m.receiver)
        }
        Expr::Call(c)
            if matches!(
                path_ident_last(&c.func).as_deref(),
                Some("from") | Some("new")
            ) && c.args.len() == 1 =>
        {
            peel(&c.args[0])
        }
        _ => expr,
    }
}

fn path_ident_last(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        Expr::Paren(p) => path_ident_last(&p.expr),
        _ => None,
    }
}

fn is_subject(expr: &Expr, subject: &str) -> bool {
    match peel(expr) {
        Expr::Path(p) => p.path.get_ident().is_some_and(|i| i == subject),
        _ => false,
    }
}

fn member_name(m: &Member) -> String {
    match m {
        Member::Named(id) => id.to_string(),
        Member::Unnamed(i) => i.index.to_string(),
    }
}

fn field_access(expr: &Expr, subject: &str) -> Option<String> {
    match peel(expr) {
        Expr::Field(f) if is_subject(&f.base, subject) => Some(member_name(&f.member)),
        _ => None,
    }
}

fn lit_str(expr: &Expr) -> Option<String> {
    match peel(expr) {
        Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }) => Some(s.value()),
        _ => None,
    }
}

type CondSplit = (Vec<(ValueCtx, String)>, Vec<(ValueCtx, String)>);

enum Cond {
    Eq { field: String, lit: String },
    In { field: String, lits: Vec<String> },
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
}

fn parse_cond(
    cond: &Expr,
    tuple_subject: Option<&str>,
    binds: &BTreeMap<String, String>,
) -> Option<Cond> {
    let cond = peel(cond);
    if let Expr::Binary(b) = cond {
        if matches!(b.op, BinOp::And(_)) {
            return Some(Cond::And(
                Box::new(parse_cond(&b.left, tuple_subject, binds)?),
                Box::new(parse_cond(&b.right, tuple_subject, binds)?),
            ));
        }
        if matches!(b.op, BinOp::Or(_)) {
            return Some(Cond::Or(
                Box::new(parse_cond(&b.left, tuple_subject, binds)?),
                Box::new(parse_cond(&b.right, tuple_subject, binds)?),
            ));
        }
    }
    if let Some((field, lit)) = eq_field_lit(cond, tuple_subject, binds) {
        return Some(Cond::Eq { field, lit });
    }
    if let Some((field, lits)) = matches_field_lits(cond, tuple_subject, binds) {
        return Some(Cond::In { field, lits });
    }
    None
}

fn resolve_field(
    expr: &Expr,
    tuple_subject: Option<&str>,
    binds: &BTreeMap<String, String>,
) -> Option<String> {
    if let Some(sub) = tuple_subject {
        if let Some(f) = field_access(expr, sub) {
            return Some(f);
        }
    }
    match peel(expr) {
        Expr::Path(p) => binds.get(&p.path.get_ident()?.to_string()).cloned(),
        _ => None,
    }
}

fn eq_field_lit(
    cond: &Expr,
    tuple_subject: Option<&str>,
    binds: &BTreeMap<String, String>,
) -> Option<(String, String)> {
    let Expr::Binary(b) = peel(cond) else {
        return None;
    };
    if !matches!(b.op, BinOp::Eq(_)) {
        return None;
    }
    if let Some(f) = resolve_field(&b.left, tuple_subject, binds) {
        return Some((f, lit_str(&b.right)?));
    }
    if let Some(f) = resolve_field(&b.right, tuple_subject, binds) {
        return Some((f, lit_str(&b.left)?));
    }
    None
}

fn matches_field_lits(
    cond: &Expr,
    tuple_subject: Option<&str>,
    binds: &BTreeMap<String, String>,
) -> Option<(String, Vec<String>)> {
    let Expr::Macro(m) = peel(cond) else {
        return None;
    };
    if !m.mac.path.is_ident("matches") {
        return None;
    }
    let parsed: MatchesArgs = syn::parse2(m.mac.tokens.clone()).ok()?;
    let field = resolve_field(&parsed.expr, tuple_subject, binds)?;
    let lits = match pat_str_lits(&parsed.pat) {
        Some(lits) if !lits.is_empty() => lits,
        _ => parsed.guard_lits?,
    };
    if lits.is_empty() {
        return None;
    }
    Some((field, lits))
}

struct MatchesArgs {
    expr: Expr,
    pat: Pat,
    guard_lits: Option<Vec<String>>,
}

impl syn::parse::Parse for MatchesArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let expr: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pat = Pat::parse_multi(input)?;
        let guard_lits = if input.peek(Token![if]) {
            input.parse::<Token![if]>()?;
            let guard: Expr = input.parse()?;
            Some(
                eq_str_lits(&guard)
                    .ok_or_else(|| input.error("expected matches! guard `x == \"…\"`"))?,
            )
        } else {
            None
        };
        let _ = input.parse::<Token![,]>();
        Ok(MatchesArgs {
            expr,
            pat,
            guard_lits,
        })
    }
}

fn eq_str_lits(expr: &Expr) -> Option<Vec<String>> {
    let Expr::Binary(b) = peel(expr) else {
        return None;
    };
    if !matches!(b.op, BinOp::Eq(_)) {
        return None;
    }
    lit_str(&b.left)
        .or_else(|| lit_str(&b.right))
        .map(|s| vec![s])
}

fn pat_str_lits(pat: &Pat) -> Option<Vec<String>> {
    match pat {
        Pat::Or(o) => {
            let mut out = Vec::new();
            for c in &o.cases {
                out.extend(pat_str_lits(c)?);
            }
            Some(out)
        }
        Pat::TupleStruct(t) => {
            let last = t.path.segments.last()?.ident.to_string();
            if last != "Some" && last != "Single" {
                return None;
            }
            pat_str_lits(t.elems.first()?)
        }
        Pat::Lit(l) => match &l.lit {
            Lit::Str(s) => Some(vec![s.value()]),
            _ => None,
        },
        _ => None,
    }
}

fn fact_of(expr: &Expr) -> Fact {
    let expr = peel(expr);
    match expr {
        Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }) => Fact::Lit(s.value()),
        Expr::Path(p) if p.path.is_ident("None") => Fact::Absent,
        Expr::Call(c)
            if matches!(
                path_last(&c.func).as_deref(),
                Some("Some") | Some("Single") | Some("Multiple")
            ) =>
        {
            c.args.first().map(fact_of).unwrap_or(Fact::Unknown)
        }
        Expr::Call(c) if is_string_new(&c.func) && c.args.is_empty() => Fact::Lit(String::new()),
        Expr::Macro(m) if m.mac.path.is_ident("format") => fact_of_format(&m.mac),
        Expr::Macro(m) if m.mac.path.is_ident("vec") => fact_of_vec_mac(&m.mac),
        Expr::Array(a) => Fact::Array(a.elems.iter().map(fact_of).collect()),
        Expr::Struct(s) => fact_of_struct(s),
        _ => Fact::Unknown,
    }
}

fn fact_of_struct(s: &syn::ExprStruct) -> Fact {
    let mut m = std::collections::BTreeMap::new();
    for f in &s.fields {
        let syn::Member::Named(id) = &f.member else {
            continue;
        };
        m.insert(id.to_string(), fact_of(&f.expr));
    }
    Fact::Record(m)
}

fn fact_of_vec_mac(mac: &syn::Macro) -> Fact {
    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let Ok(args) = parser.parse2(mac.tokens.clone()) else {
        return Fact::Array(vec![]);
    };
    Fact::Array(args.iter().map(fact_of).collect())
}

fn is_string_new(func: &Expr) -> bool {
    let Expr::Path(p) = peel(func) else {
        return false;
    };
    let segs: Vec<_> = p
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    segs.windows(2).any(|w| w[0] == "String" && w[1] == "new")
}

fn fact_of_format(mac: &syn::Macro) -> Fact {
    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let Ok(args) = parser.parse2(mac.tokens.clone()) else {
        return Fact::Unknown;
    };
    let mut args = args.into_iter();
    let Some(fmt) = args.next().as_ref().and_then(lit_str) else {
        return Fact::Unknown;
    };
    let mut lits = Vec::new();
    for a in args {
        match fact_of(&a) {
            Fact::Lit(s) => lits.push(s),
            _ => return Fact::Unknown,
        }
    }
    match fill_braces(&fmt, &lits) {
        Some(s) => Fact::Lit(s),
        None => Fact::Unknown,
    }
}

fn fill_braces(fmt: &str, args: &[String]) -> Option<String> {
    let mut out = String::new();
    let mut chars = fmt.chars().peekable();
    let mut i = 0;
    while let Some(c) = chars.next() {
        if c == '{' {
            match chars.peek() {
                Some('{') => {
                    chars.next();
                    out.push('{');
                }
                Some('}') => {
                    chars.next();
                    out.push_str(args.get(i)?);
                    i += 1;
                }
                _ => return None,
            }
        } else if c == '}' {
            if chars.peek() == Some(&'}') {
                chars.next();
                out.push('}');
            } else {
                return None;
            }
        } else {
            out.push(c);
        }
    }
    (i == args.len()).then_some(out)
}

fn path_last(expr: &Expr) -> Option<String> {
    match peel(expr) {
        Expr::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        _ => None,
    }
}

fn called_name(expr: &Expr) -> Option<String> {
    match peel(expr) {
        Expr::Call(c) => path_last(&c.func),
        Expr::MethodCall(m) => Some(m.method.to_string()),
        _ => None,
    }
}

fn call_touches_subject(expr: &Expr, subject: &str) -> bool {
    match peel(expr) {
        Expr::Call(c) => c.args.iter().any(|a| is_subject(a, subject)),
        Expr::MethodCall(m) => is_subject(&m.receiver, subject),
        _ => false,
    }
}

fn is_default(expr: &Expr) -> bool {
    let Expr::Call(c) = peel(expr) else {
        return false;
    };
    let Expr::Path(p) = peel(&c.func) else {
        return false;
    };
    p.path.segments.last().is_some_and(|s| s.ident == "default")
}
