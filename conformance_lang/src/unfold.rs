//! Unfold — one Observe backend. Walk `self` / `m` rewrite; path-split;
//! follow Known callee writes. Not the camera: layout and live Observe
//! never enter here.

use std::collections::BTreeMap;

use syn::punctuated::Punctuated;
use syn::{
    parse_str, BinOp, Block, Expr, ExprLit, FnArg, ImplItem, Item, ItemImpl, Lit, Member, Pat,
    Stmt, Token, Type,
};

use crate::ir::{Schema, ValueCtx};
use crate::observe::Fact;
use crate::{eval_schema, CheckReport};

const FOLLOW_DEPTH: usize = 8;

/// One path's snapshot of the schema value.
#[derive(Debug, Clone)]
pub struct Observation {
    pub label: String,
    pub ctx: ValueCtx,
}

struct FnDef {
    name: String,
    subject: String,
    block: Block,
}

struct Path {
    label: String,
    ctx: ValueCtx,
    done: bool,
}

struct Engine<'a> {
    schema: &'a Schema,
    fns: &'a BTreeMap<String, FnDef>,
    subject: &'a str,
    depth: usize,
}

/// Parse `source`, observe every fn that rewrites a value of `schema`'s type.
pub fn unfold(schema: &Schema, source: &str) -> Result<Vec<Observation>, String> {
    let file: syn::File = parse_str(source).map_err(|e| e.to_string())?;
    let fns = collect_fns(&file, schema);
    let mut out = Vec::new();
    for def in fns.values() {
        let engine = Engine {
            schema,
            fns: &fns,
            subject: &def.subject,
            depth: 0,
        };
        out.extend(engine.run(def));
    }
    Ok(out)
}

pub fn eval_unfold(schema: &Schema, source: &str) -> Result<CheckReport, String> {
    let mut report = CheckReport::default();
    for ob in unfold(schema, source)? {
        report
            .findings
            .extend(eval_schema(schema, &ob.ctx, Some(&ob.label)).findings);
    }
    Ok(report)
}

/// Unfold `source`, eval only paths that belong to `name` (and its `then`/`else` crumbs).
/// Callees followed from that fn are included; other top-level fns are not.
pub fn eval_unfold_named(schema: &Schema, source: &str, name: &str) -> Result<CheckReport, String> {
    let mut report = CheckReport::default();
    let prefix = format!("{name}.");
    let mut any = false;
    for ob in unfold(schema, source)? {
        if ob.label == name || ob.label.starts_with(&prefix) {
            any = true;
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

fn collect_fns(file: &syn::File, schema: &Schema) -> BTreeMap<String, FnDef> {
    let mut fns = BTreeMap::new();
    for item in &file.items {
        match item {
            Item::Fn(f) => {
                if let Some(def) = fn_from_parts(
                    f.sig.ident.to_string(),
                    &f.sig.inputs,
                    &f.block,
                    None,
                    schema,
                ) {
                    fns.insert(def.name.clone(), def);
                }
            }
            Item::Impl(im) => collect_impl(&mut fns, im, schema),
            _ => {}
        }
    }
    fns
}

fn collect_impl(fns: &mut BTreeMap<String, FnDef>, im: &ItemImpl, schema: &Schema) {
    let impl_ty = type_last_ident(&im.self_ty);
    let impl_ty = impl_ty.as_deref().filter(|t| *t == schema.name.as_str());
    for item in &im.items {
        let ImplItem::Fn(m) = item else { continue };
        if let Some(def) = fn_from_parts(
            m.sig.ident.to_string(),
            &m.sig.inputs,
            &m.block,
            impl_ty,
            schema,
        ) {
            fns.insert(def.name.clone(), def);
        }
    }
}

fn fn_from_parts(
    name: String,
    inputs: &Punctuated<FnArg, Token![,]>,
    block: &Block,
    impl_ty: Option<&str>,
    schema: &Schema,
) -> Option<FnDef> {
    for input in inputs {
        match input {
            FnArg::Receiver(_) if impl_ty == Some(schema.name.as_str()) => {
                return Some(FnDef {
                    name,
                    subject: "self".into(),
                    block: block.clone(),
                });
            }
            FnArg::Typed(pat) => {
                if type_last_ident(&pat.ty).as_deref() != Some(schema.name.as_str()) {
                    continue;
                }
                let Pat::Ident(id) = &*pat.pat else { continue };
                return Some(FnDef {
                    name,
                    subject: id.ident.to_string(),
                    block: block.clone(),
                });
            }
            _ => {}
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
            })
            .collect()
    }

    fn exec_block(&self, block: &Block, ctx: ValueCtx, label: String) -> Vec<Path> {
        self.exec_seq(&block.stmts, ctx, label)
    }

    fn exec_seq(&self, stmts: &[Stmt], ctx: ValueCtx, label: String) -> Vec<Path> {
        let Some((head, tail)) = stmts.split_first() else {
            return vec![Path {
                ctx,
                label,
                done: false,
            }];
        };
        let continue_with = |paths: Vec<Path>| -> Vec<Path> {
            paths
                .into_iter()
                .flat_map(|p| {
                    if p.done || tail.is_empty() {
                        vec![p]
                    } else {
                        self.exec_seq(tail, p.ctx, p.label)
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
                let ctx = self.exec_local(local, ctx);
                continue_with(vec![Path {
                    ctx,
                    label,
                    done: false,
                }])
            }
            _ => continue_with(vec![Path {
                ctx,
                label,
                done: false,
            }]),
        }
    }

    fn exec_local(&self, local: &syn::Local, ctx: ValueCtx) -> ValueCtx {
        let Some(init) = &local.init else { return ctx };
        let Pat::Ident(id) = &local.pat else {
            return ctx;
        };
        if id.ident != self.subject {
            return ctx;
        }
        self.apply_value(&init.expr, ctx)
            .into_iter()
            .next()
            .expect("apply_value yields a path")
            .ctx
    }

    fn exec_if(&self, i: &syn::ExprIf, ctx: ValueCtx, label: String, as_return: bool) -> Vec<Path> {
        let (then_ctx, else_ctx, then_l, else_l) = self.split_if(&i.cond, ctx, &label);
        let mut then_ps = self.exec_block(&i.then_branch, then_ctx, then_l);
        let mut else_ps = match &i.else_branch {
            Some((_, e)) => self.exec_expr(e, else_ctx, else_l, as_return),
            None => vec![Path {
                ctx: else_ctx,
                label: else_l,
                done: false,
            }],
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
                None => vec![Path {
                    ctx,
                    label,
                    done: true,
                }],
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
                    return vec![Path {
                        ctx: ctx.put(&name, fact_of(&a.right)),
                        label,
                        done: false,
                    }];
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
        vec![Path {
            ctx,
            label,
            done: false,
        }]
    }

    fn apply_value(&self, expr: &Expr, ctx: ValueCtx) -> Vec<Path> {
        let expr = peel(expr);
        if is_default(expr) {
            return vec![Path {
                ctx: self.unknown_all(ctx),
                label: String::new(),
                done: false,
            }];
        }
        if let Expr::Struct(s) = expr {
            return vec![Path {
                ctx: self.apply_struct(s, ctx),
                label: String::new(),
                done: false,
            }];
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
        vec![Path {
            ctx,
            label: String::new(),
            done: false,
        }]
    }

    fn try_follow(&self, expr: &Expr, ctx: ValueCtx) -> Option<Vec<Path>> {
        if self.depth >= FOLLOW_DEPTH {
            return None;
        }
        let name = called_name(expr)?;
        let def = self.fns.get(&name)?;
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

    fn split_if(
        &self,
        cond: &Expr,
        ctx: ValueCtx,
        label: &str,
    ) -> (ValueCtx, ValueCtx, String, String) {
        if let Some((field, lit)) = eq_field_lit(cond, self.subject) {
            if self.has_field(&field) {
                let then_l = format!("{label}.then[{field}=={lit}]");
                let else_l = format!("{label}.else[{field}=={lit}]");
                return (
                    ctx.clone().lit(&field, lit.clone()),
                    ctx.exclude(&field, lit),
                    then_l,
                    else_l,
                );
            }
        }
        if let Some((field, lits)) = matches_field_lits(cond, self.subject) {
            if self.has_field(&field) {
                let then_l = format!("{label}.then[{field} in {lits:?}]");
                let else_l = format!("{label}.else[{field} in {lits:?}]");
                let then_ctx = ctx.clone().one_of(&field, lits.clone());
                let else_ctx = lits.iter().fold(ctx, |c, l| c.exclude(&field, l));
                return (then_ctx, else_ctx, then_l, else_l);
            }
        }
        (
            ctx.clone(),
            ctx,
            format!("{label}.then"),
            format!("{label}.else"),
        )
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

fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(p) => peel(&p.expr),
        Expr::Reference(r) => peel(&r.expr),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => peel(&u.expr),
        Expr::MethodCall(m)
            if matches!(
                m.method.to_string().as_str(),
                "into" | "to_string" | "to_owned" | "clone" | "as_deref" | "as_str" | "as_ref"
            ) =>
        {
            peel(&m.receiver)
        }
        _ => expr,
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

fn eq_field_lit(cond: &Expr, subject: &str) -> Option<(String, String)> {
    let Expr::Binary(b) = peel(cond) else {
        return None;
    };
    if !matches!(b.op, BinOp::Eq(_)) {
        return None;
    }
    if let Some(f) = field_access(&b.left, subject) {
        return Some((f, lit_str(&b.right)?));
    }
    if let Some(f) = field_access(&b.right, subject) {
        return Some((f, lit_str(&b.left)?));
    }
    None
}

fn matches_field_lits(cond: &Expr, subject: &str) -> Option<(String, Vec<String>)> {
    let Expr::Macro(m) = peel(cond) else {
        return None;
    };
    if !m.mac.path.is_ident("matches") {
        return None;
    }
    let parsed: MatchesArgs = syn::parse2(m.mac.tokens.clone()).ok()?;
    let field = field_access(&parsed.expr, subject)?;
    let lits = pat_str_lits(&parsed.pat)?;
    if lits.is_empty() {
        return None;
    }
    Some((field, lits))
}

struct MatchesArgs {
    expr: Expr,
    pat: Pat,
}

impl syn::parse::Parse for MatchesArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let expr: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pat = Pat::parse_multi(input)?;
        let _ = input.parse::<Token![,]>();
        Ok(MatchesArgs { expr, pat })
    }
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
            if last != "Some" {
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
        Expr::Call(c) if path_last(&c.func).as_deref() == Some("Some") => {
            c.args.first().map(fact_of).unwrap_or(Fact::Unknown)
        }
        Expr::Macro(m) if m.mac.path.is_ident("vec") => Fact::Array,
        Expr::Array(_) => Fact::Array,
        _ => Fact::Unknown,
    }
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
