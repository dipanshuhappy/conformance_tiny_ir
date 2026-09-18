//! Evaluate Invariants of a Schema against one observed state (`ValueCtx`).

use crate::absval::AbsVal;
use crate::ir::{Field, Form, Invariant, Predicate, Schema, ValueCtx};

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

#[derive(Debug, Default)]
pub struct CheckReport {
    pub findings: Vec<Finding>,
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
            push_eval(
                &mut report,
                schema,
                &field.name,
                site_label,
                eval_invariant_expanded(ctx, field, prop),
            );
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
            let mut last = EvalError::Fail("Invariant any: empty".into());
            for p in props {
                match eval_invariant(ctx, field, p) {
                    Ok(()) => return Ok(()),
                    Err(e) => last = e,
                }
            }
            Err(last)
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
        (Form::Array, AbsVal::Array) => Ok(()),
        (Form::Scalar, AbsVal::Array) => Err(EvalError::Fail(format!(
            "Invariant shape failed: `{field}` is array, expected scalar"
        ))),
        (Form::Array, AbsVal::Known(_) | AbsVal::OneOf(_)) => Err(EvalError::Fail(format!(
            "Invariant shape failed: `{field}` is scalar, expected array"
        ))),
    }
}

fn eval_one_of(ctx: &ValueCtx, field: &str, allowed: &[String]) -> Result<(), EvalError> {
    let Some(val) = ctx.values.get(field) else {
        return Err(EvalError::Undecidable(format!(
            "Invariant oneOf: `{field}` unobserved"
        )));
    };
    match val {
        AbsVal::Absent => Err(EvalError::Fail(format!(
            "Invariant oneOf failed: `{field}` is absent (not in {allowed:?})"
        ))),
        AbsVal::Unknown => Err(EvalError::Undecidable(format!(
            "Invariant oneOf on `{field}`: value Unknown"
        ))),
        AbsVal::Array => Err(EvalError::Fail(format!(
            "Invariant oneOf failed: `{field}` is array, not a scalar in {allowed:?}"
        ))),
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
            Some(AbsVal::Unknown | AbsVal::Array) => Err(EvalError::Undecidable(format!(
                "Predicate {field}=={lit:?}: not a known scalar"
            ))),
            Some(AbsVal::Known(s)) => Ok(s == lit),
            Some(AbsVal::OneOf(set)) => Ok(set.iter().any(|s| s == lit)),
        },
        Predicate::In { field, lits } => match ctx.values.get(field) {
            None if lits.iter().all(|l| excluded(ctx, field, l)) => Ok(false),
            None => Err(EvalError::Undecidable(format!(
                "Predicate {field} in {lits:?}: unobserved"
            ))),
            Some(AbsVal::Absent) => Ok(false),
            Some(AbsVal::Unknown | AbsVal::Array) => Err(EvalError::Undecidable(format!(
                "Predicate {field} in {lits:?}: not a known scalar"
            ))),
            Some(AbsVal::Known(s)) => Ok(lits.iter().any(|l| l == s)),
            Some(AbsVal::OneOf(set)) => Ok(set.iter().any(|s| lits.iter().any(|l| l == s))),
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
