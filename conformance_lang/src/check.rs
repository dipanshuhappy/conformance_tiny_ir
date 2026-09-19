//! Evaluate Invariants of a Schema against one observed state (`ValueCtx`).

use crate::absval::AbsVal;
use crate::ir::{Field, Form, Invariant, Locator, Predicate, Rewrite, Schema, ValueCtx};
use crate::observe::Fact;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FindingKind {
    Fail,
    Undecidable,
}

#[derive(Debug, Clone)]
pub struct Finding {
    pub kind: FindingKind,
    pub schema: String,
    pub field: String,
    pub message: String,
    pub site: Option<String>,
}

/// A site muted by `#[except("…")]`. Not a Fail. Follow into that fn still runs.
#[derive(Debug, Clone)]
pub struct Skip {
    pub site: String,
    pub reason: String,
}

#[derive(Debug, Default, Clone)]
pub struct CheckReport {
    pub findings: Vec<Finding>,
    pub skipped: Vec<Skip>,
}

impl CheckReport {
    pub fn fails(&self) -> impl Iterator<Item = &Finding> {
        self.findings.iter().filter(|f| f.kind == FindingKind::Fail)
    }

    pub fn ok(&self) -> bool {
        self.fails().next().is_none()
    }

    pub fn fail_summary(&self) -> String {
        self.fails()
            .map(|f| match &f.site {
                Some(site) => format!("  {} @ {site}: {}", f.field, f.message),
                None => format!("  {}: {}", f.field, f.message),
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    pub fn merge(&mut self, other: CheckReport) {
        self.findings.extend(other.findings);
        self.skipped.extend(other.skipped);
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("{0}")]
    Fail(String),
    #[error("undecidable: {0}")]
    Undecidable(String),
}

/// Eval every field invariant of `schema` against one `ValueCtx`.
pub fn eval_schema(schema: &Schema, ctx: &ValueCtx, site_label: Option<&str>) -> CheckReport {
    let mut report = CheckReport::default();
    for field in &schema.fields {
        for prop in &field.invariants {
            if let Some(inner) = optional_nested(prop) {
                match ctx.values.get(&field.name) {
                    Some(AbsVal::Absent) => {}
                    _ => report.merge(eval_walk(ctx, &field.name, inner, site_label)),
                }
            } else if let Invariant::Nested(inner) = prop {
                report.merge(eval_walk(ctx, &field.name, inner, site_label));
            } else {
                push_eval(
                    &mut report,
                    schema,
                    &field.name,
                    site_label,
                    eval_invariant_expanded(ctx, field, prop),
                );
            }
        }
        if let Some(w) = &field.wire {
            if let Some(pos) = w.pos {
                push_eval(
                    &mut report,
                    schema,
                    &field.name,
                    site_label,
                    eval_invariant(ctx, field, &Invariant::At(pos)),
                );
            }
            if let Some(len) = w.len {
                push_eval(
                    &mut report,
                    schema,
                    &field.name,
                    site_label,
                    eval_invariant(ctx, field, &Invariant::Width(len)),
                );
            }
        }
    }
    push_eval(
        &mut report,
        schema,
        "*",
        site_label,
        eval_tiling(schema, ctx),
    );
    report
}

/// `when(P, rewrite I)`: P on `pre`, I on `write` as `rw.field`.
pub fn eval_rewrite(
    schema: &Schema,
    rw: &Rewrite,
    pre: &ValueCtx,
    write: &Fact,
    site_label: Option<&str>,
) -> CheckReport {
    let mut report = CheckReport::default();
    match eval_predicate(pre, &rw.pred) {
        Ok(false) => report,
        Ok(true) => {
            let ctx = ValueCtx::default().put(&rw.field, write.clone());
            let field = Field {
                name: rw.field.clone(),
                locator: Locator::Path(rw.field.clone()),
                invariants: vec![],
                wire: None,
            };
            push_eval(
                &mut report,
                schema,
                &rw.field,
                site_label,
                eval_invariant(&ctx, &field, &rw.then),
            );
            report
        }
        Err(e) => {
            push_eval(&mut report, schema, &rw.field, site_label, Err(e));
            report
        }
    }
}

pub fn eval_rewrites(
    schema: &Schema,
    pre: &ValueCtx,
    field: &str,
    write: &Fact,
    site_label: Option<&str>,
) -> CheckReport {
    let mut report = CheckReport::default();
    for rw in &schema.rewrites {
        if rw.field == field {
            report.merge(eval_rewrite(schema, rw, pre, write, site_label));
        }
    }
    report
}

pub fn eval_invariant(ctx: &ValueCtx, field: &Field, prop: &Invariant) -> Result<(), EvalError> {
    match prop {
        Invariant::Defined => match ctx.values.get(&field.name) {
            None => Err(EvalError::Undecidable(format!(
                "Invariant defined: `{0}` unobserved",
                field.name
            ))),
            Some(AbsVal::Absent) => Err(EvalError::Fail(format!(
                "Invariant defined failed: field `{}` is absent",
                field.name
            ))),
            Some(AbsVal::Unknown) => Err(EvalError::Undecidable(format!(
                "Invariant defined: `{}` Unknown",
                field.name
            ))),
            Some(_) => Ok(()),
        },
        Invariant::Absent => match ctx.values.get(&field.name) {
            None => Err(EvalError::Undecidable(format!(
                "Invariant absent: `{}` unobserved",
                field.name
            ))),
            Some(AbsVal::Absent) => Ok(()),
            Some(_) => Err(EvalError::Fail(format!(
                "Invariant absent failed: field `{}` is present",
                field.name
            ))),
        },
        Invariant::OneOf(allowed) => eval_one_of(ctx, &field.name, allowed),
        Invariant::Refine(r) => eval_refine(ctx, &field.name, r),
        Invariant::Nested(inner) => eval_walk_result(ctx, &field.name, inner),
        Invariant::Unique => eval_unique(ctx, &field.name),
        Invariant::Shape(form) => eval_shape(ctx, &field.name, *form),
        Invariant::At(expected) => {
            let got = ctx
                .wire
                .get(&field.name)
                .and_then(|w| w.pos)
                .ok_or_else(|| {
                    EvalError::Undecidable(format!(
                        "Invariant at({expected}): no observed pos for `{}`",
                        field.name
                    ))
                })?;
            if got == *expected {
                Ok(())
            } else {
                Err(EvalError::Fail(format!(
                    "Invariant at({expected}) failed: observed pos {got} for `{}`",
                    field.name
                )))
            }
        }
        Invariant::Width(expected) => {
            let got = ctx
                .wire
                .get(&field.name)
                .and_then(|w| w.len)
                .ok_or_else(|| {
                    EvalError::Undecidable(format!(
                        "Invariant width({expected}): no observed len for `{}`",
                        field.name
                    ))
                })?;
            if got == *expected {
                Ok(())
            } else {
                Err(EvalError::Fail(format!(
                    "Invariant width({expected}) failed: observed len {got} for `{}`",
                    field.name
                )))
            }
        }
        Invariant::When { pred, then } => match eval_predicate(ctx, pred)? {
            true => eval_invariant(ctx, field, then),
            false => Ok(()),
        },
        Invariant::All(props) => {
            for p in props {
                eval_invariant(ctx, field, p)?;
            }
            Ok(())
        }
        Invariant::Any(props) => {
            let mut last_fail = EvalError::Fail("Invariant any: empty".into());
            let mut undecidable = None;
            for p in props {
                match eval_invariant(ctx, field, p) {
                    Ok(()) => return Ok(()),
                    Err(e @ EvalError::Undecidable(_)) => undecidable = Some(e),
                    Err(e) => last_fail = e,
                }
            }
            // `or_absent` = Any(I, Absent). Present + Unknown: I is Undecidable,
            // Absent is Fail — keep Undecidable, not “absent failed”.
            Err(undecidable.unwrap_or(last_fail))
        }
    }
}

fn eval_shape(ctx: &ValueCtx, field: &str, form: Form) -> Result<(), EvalError> {
    let Some(val) = ctx.values.get(field) else {
        return Err(EvalError::Undecidable(format!(
            "Invariant shape: `{field}` unobserved"
        )));
    };
    match (form, val) {
        (_, AbsVal::Unknown) => Err(EvalError::Undecidable(format!(
            "Invariant shape: `{field}` Unknown"
        ))),
        (_, AbsVal::Absent) => Err(EvalError::Fail(format!(
            "Invariant shape failed: `{field}` is absent"
        ))),
        (Form::Scalar, AbsVal::Known(_) | AbsVal::OneOf(_)) => Ok(()),
        (Form::Array, AbsVal::Array(_)) => Ok(()),
        (Form::Scalar, AbsVal::Array(_) | AbsVal::Record(_)) => Err(EvalError::Fail(format!(
            "Invariant shape failed: `{field}` is not scalar"
        ))),
        (Form::Array, AbsVal::Known(_) | AbsVal::OneOf(_) | AbsVal::Record(_)) => {
            Err(EvalError::Fail(format!(
                "Invariant shape failed: `{field}` is not array"
            )))
        }
    }
}

fn eval_refine(
    ctx: &ValueCtx,
    field: &str,
    r: &crate::ir::RefineFn,
) -> Result<(), EvalError> {
    let Some(val) = ctx.values.get(field) else {
        return Err(EvalError::Undecidable(format!(
            "Invariant refine: `{field}` unobserved"
        )));
    };
    r.run(val).map_err(|e| match e {
        crate::absval::ApplyErr::Fail(m) => {
            EvalError::Fail(format!("Invariant refine failed: `{field}` {m}"))
        }
        crate::absval::ApplyErr::Undecidable(m) => {
            EvalError::Undecidable(format!("Invariant refine on `{field}`: {m}"))
        }
    })
}

fn eval_one_of(ctx: &ValueCtx, field: &str, allowed: &[String]) -> Result<(), EvalError> {
    let Some(val) = ctx.values.get(field) else {
        return Err(EvalError::Undecidable(format!(
            "Invariant oneOf: `{field}` unobserved"
        )));
    };
    eval_one_of_val(field, allowed, val)
}

fn eval_one_of_val(field: &str, allowed: &[String], val: &AbsVal) -> Result<(), EvalError> {
    match val {
        AbsVal::Absent => Err(EvalError::Fail(format!(
            "Invariant oneOf failed: `{field}` is absent (not in {allowed:?})"
        ))),
        AbsVal::Unknown => Err(EvalError::Undecidable(format!(
            "Invariant oneOf on `{field}`: value Unknown"
        ))),
        AbsVal::Record(_) => Err(EvalError::Fail(format!(
            "Invariant oneOf failed: `{field}` is a record"
        ))),
        AbsVal::Array(xs) => {
            let mut und = None;
            for x in xs {
                match eval_one_of_val(field, allowed, x) {
                    Ok(()) => {}
                    Err(EvalError::Fail(m)) => return Err(EvalError::Fail(m)),
                    Err(e) => und = Some(e),
                }
            }
            match und {
                Some(e) => Err(e),
                None => Ok(()),
            }
        }
        AbsVal::Known(s) => {
            if allowed.iter().any(|a| a == s) {
                Ok(())
            } else {
                Err(EvalError::Fail(format!(
                    "Invariant oneOf failed: `{field}` = {s:?} not in {allowed:?}"
                )))
            }
        }
        AbsVal::OneOf(set) => {
            for s in set {
                if !allowed.iter().any(|a| a == s) {
                    return Err(EvalError::Fail(format!(
                        "Invariant oneOf failed: `{field}` can be {s:?} not in {allowed:?}"
                    )));
                }
            }
            Ok(())
        }
    }
}

fn eval_unique(ctx: &ValueCtx, field: &str) -> Result<(), EvalError> {
    let Some(val) = ctx.values.get(field) else {
        return Err(EvalError::Undecidable(format!(
            "Invariant unique: `{field}` unobserved"
        )));
    };
    match val {
        AbsVal::Unknown => Err(EvalError::Undecidable(format!(
            "Invariant unique on `{field}`: value Unknown"
        ))),
        AbsVal::Absent => Err(EvalError::Fail(format!(
            "Invariant unique failed: `{field}` is absent"
        ))),
        AbsVal::Known(_) | AbsVal::OneOf(_) | AbsVal::Record(_) => Ok(()),
        AbsVal::Array(xs) => {
            let mut seen = std::collections::BTreeSet::new();
            let mut und = false;
            for x in xs {
                match x {
                    AbsVal::Known(s) => {
                        if !seen.insert(s.clone()) {
                            return Err(EvalError::Fail(format!(
                                "Invariant unique failed: `{field}` duplicates {s:?}"
                            )));
                        }
                    }
                    AbsVal::Unknown => und = true,
                    _ => {}
                }
            }
            if und {
                Err(EvalError::Undecidable(format!(
                    "Invariant unique on `{field}`: element Unknown"
                )))
            } else {
                Ok(())
            }
        }
    }
}

fn excluded(ctx: &ValueCtx, field: &str, lit: &str) -> bool {
    ctx.excluded
        .get(field)
        .map(|s| s.contains(lit))
        .unwrap_or(false)
}

fn eval_predicate(ctx: &ValueCtx, pred: &Predicate) -> Result<bool, EvalError> {
    match pred {
        Predicate::Eq { field, lit } => match ctx.values.get(field) {
            None if excluded(ctx, field, lit) => Ok(false),
            None => Err(EvalError::Undecidable(format!(
                "Predicate {field}=={lit:?}: unobserved"
            ))),
            Some(AbsVal::Absent) => Ok(false),
            Some(AbsVal::Unknown | AbsVal::Array(_) | AbsVal::Record(_)) => {
                Err(EvalError::Undecidable(format!(
                    "Predicate {field}=={lit:?}: not a known scalar"
                )))
            }
            Some(AbsVal::Known(s)) => Ok(s == lit),
            Some(AbsVal::OneOf(set)) => Ok(set.iter().any(|s| s == lit)),
        },
        Predicate::In { field, lits } => match ctx.values.get(field) {
            None if lits.iter().all(|l| excluded(ctx, field, l)) => Ok(false),
            None => Err(EvalError::Undecidable(format!(
                "Predicate {field} in {lits:?}: unobserved"
            ))),
            Some(AbsVal::Absent) => Ok(false),
            Some(AbsVal::Unknown | AbsVal::Array(_) | AbsVal::Record(_)) => {
                Err(EvalError::Undecidable(format!(
                    "Predicate {field} in {lits:?}: not a known scalar"
                )))
            }
            Some(AbsVal::Known(s)) => Ok(lits.iter().any(|l| l == s)),
            Some(AbsVal::OneOf(set)) => Ok(set.iter().any(|s| lits.iter().any(|l| l == s))),
        },
        Predicate::Defined { field } => match ctx.values.get(field) {
            None => Err(EvalError::Undecidable(format!(
                "Predicate {field} defined: unobserved"
            ))),
            Some(AbsVal::Absent) => Ok(false),
            Some(_) => Ok(true),
        },
        Predicate::And(xs) => {
            for x in xs {
                if !eval_predicate(ctx, x)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Predicate::Or(xs) => {
            for x in xs {
                if eval_predicate(ctx, x)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Predicate::Not(x) => Ok(!eval_predicate(ctx, x)?),
    }
}

/// When Predicate is Eq/In on a OneOf field, bind each candidate and eval `then`.
fn optional_nested(prop: &Invariant) -> Option<&Schema> {
    let Invariant::Any(xs) = prop else {
        return None;
    };
    let mut inner = None;
    let mut absent = false;
    for x in xs {
        match x {
            Invariant::Nested(s) => inner = Some(s.as_ref()),
            Invariant::Absent => absent = true,
            _ => return None,
        }
    }
    if absent {
        inner
    } else {
        None
    }
}

fn eval_walk(
    ctx: &ValueCtx,
    field: &str,
    inner: &Schema,
    site: Option<&str>,
) -> CheckReport {
    let Some(val) = ctx.values.get(field) else {
        let mut r = CheckReport::default();
        push_eval(
            &mut r,
            inner,
            field,
            site,
            Err(EvalError::Undecidable(format!(
                "nested `{}`: `{field}` unobserved",
                inner.name
            ))),
        );
        return r;
    };
    eval_walk_val(field, val, inner, site)
}

fn eval_walk_val(
    path: &str,
    val: &AbsVal,
    inner: &Schema,
    site: Option<&str>,
) -> CheckReport {
    match val {
        AbsVal::Absent => {
            let mut r = CheckReport::default();
            push_eval(
                &mut r,
                inner,
                path,
                site,
                Err(EvalError::Fail(format!(
                    "nested `{}` failed: `{path}` is absent",
                    inner.name
                ))),
            );
            r
        }
        AbsVal::Unknown => {
            let mut r = CheckReport::default();
            push_eval(
                &mut r,
                inner,
                path,
                site,
                Err(EvalError::Undecidable(format!(
                    "nested `{}` on `{path}`: Unknown",
                    inner.name
                ))),
            );
            r
        }
        AbsVal::Record(map) => {
            let sub = ValueCtx {
                values: map.clone(),
                ..ValueCtx::default()
            };
            prefix_report(path, eval_schema(inner, &sub, site))
        }
        AbsVal::Array(xs) => {
            let mut out = CheckReport::default();
            for (i, x) in xs.iter().enumerate() {
                out.merge(eval_walk_val(&format!("{path}[{i}]"), x, inner, site));
            }
            out
        }
        _ => {
            let mut r = CheckReport::default();
            push_eval(
                &mut r,
                inner,
                path,
                site,
                Err(EvalError::Fail(format!(
                    "nested `{}` failed: `{path}` is not a record",
                    inner.name
                ))),
            );
            r
        }
    }
}

fn prefix_report(parent: &str, mut report: CheckReport) -> CheckReport {
    for f in &mut report.findings {
        f.field = format!("{parent}.{}", f.field);
    }
    report
}

fn eval_walk_result(ctx: &ValueCtx, field: &str, inner: &Schema) -> Result<(), EvalError> {
    let r = eval_walk(ctx, field, inner, None);
    if let Some(f) = r.fails().next() {
        return Err(EvalError::Fail(f.message.clone()));
    }
    if let Some(f) = r
        .findings
        .iter()
        .find(|f| f.kind == FindingKind::Undecidable)
    {
        return Err(EvalError::Undecidable(f.message.clone()));
    }
    Ok(())
}

fn eval_invariant_expanded(
    ctx: &ValueCtx,
    field: &Field,
    prop: &Invariant,
) -> Result<(), EvalError> {
    if let Invariant::When { pred, then } = prop {
        if let Some(arms) = expand_oneof_pred(ctx, pred) {
            for arm in arms {
                if eval_predicate(&arm, pred)? {
                    eval_invariant(&arm, field, then)?;
                }
            }
            return Ok(());
        }
    }
    eval_invariant(ctx, field, prop)
}

fn expand_oneof_pred(ctx: &ValueCtx, pred: &Predicate) -> Option<Vec<ValueCtx>> {
    let field = match pred {
        Predicate::Eq { field, .. } | Predicate::In { field, .. } => field,
        _ => return None,
    };
    let AbsVal::OneOf(set) = ctx.values.get(field)? else {
        return None;
    };
    Some(
        set.iter()
            .map(|c| {
                let mut arm = ctx.clone();
                arm.values.insert(field.clone(), AbsVal::Known(c.clone()));
                arm
            })
            .collect(),
    )
}

/// Painted spans must sit on the tape and not overlap. Holes are padding.
fn eval_tiling(schema: &Schema, ctx: &ValueCtx) -> Result<(), EvalError> {
    let Some(n) = schema.width else {
        return Ok(());
    };
    let spans: Vec<(&str, usize, usize)> = schema
        .fields
        .iter()
        .filter_map(|f| {
            let w = ctx.wire.get(&f.name)?;
            Some((f.name.as_str(), w.pos?, w.len?))
        })
        .collect();
    if spans.is_empty() {
        return Ok(());
    }

    let mut cover: Vec<Option<&str>> = vec![None; n];
    for (name, pos, len) in &spans {
        if *pos == 0 {
            return Err(EvalError::Fail(format!(
                "tiling: `{name}` pos is 0 (positions are 1-based)"
            )));
        }
        let start = pos - 1;
        if start.saturating_add(*len) > n {
            return Err(EvalError::Fail(format!(
                "tiling: `{name}` [{pos}..{end}) past width {n}",
                end = pos + len
            )));
        }
        for (offset, slot) in cover[start..start + *len].iter_mut().enumerate() {
            if let Some(other) = *slot {
                return Err(EvalError::Fail(format!(
                    "tiling: `{name}` overlaps `{other}` at pos {}",
                    start + offset + 1
                )));
            }
            *slot = Some(*name);
        }
    }
    Ok(())
}

fn push_eval(
    report: &mut CheckReport,
    schema: &Schema,
    field: &str,
    site_label: Option<&str>,
    result: Result<(), EvalError>,
) {
    match result {
        Ok(()) => {}
        Err(EvalError::Fail(message)) => report.findings.push(Finding {
            kind: FindingKind::Fail,
            schema: schema.name.clone(),
            field: field.to_string(),
            message,
            site: site_label.map(str::to_string),
        }),
        Err(EvalError::Undecidable(message)) => report.findings.push(Finding {
            kind: FindingKind::Undecidable,
            schema: schema.name.clone(),
            field: field.to_string(),
            message,
            site: site_label.map(str::to_string),
        }),
    }
}
