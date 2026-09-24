//! Stdlib invariants — not new primitives.

use crate::ir::{Form, Invariant, Predicate, Refine, Rewrite, Schema};

pub fn one_of(values: &[&str]) -> Invariant {
    Invariant::OneOf(values.iter().map(|s| (*s).to_string()).collect())
}

pub fn defined() -> Invariant {
    Invariant::Defined
}

pub fn absent() -> Invariant {
    Invariant::Absent
}

/// `I || None` — Option sugar. `enum_` stays `one_of`. Erase happens here (Schema).
pub fn or_absent(inv: impl Into<Invariant>) -> Invariant {
    Invariant::Any(vec![inv.into(), Invariant::Absent])
}

/// `Refine a → Refine a → Refine a` (And).
pub fn all<A: ?Sized>(a: Refine<A>, b: Refine<A>) -> Refine<A> {
    Refine::pack(Invariant::All(vec![a.into(), b.into()]))
}

/// `Refine str`. rustc cannot infer a generic `a` from `|x|`; this is that inhabitant.
pub fn refine(check: impl Fn(&str) -> bool + Send + Sync + 'static) -> Refine<str> {
    refine_on::<str>(check)
}

/// Full-string regular-expression sugar for `Refine str`.
///
/// The pattern is compiled once when the Schema is built. It is wrapped in
/// `\A(?:...)\z`, so callers cannot accidentally request a substring match.
pub fn matches(pattern: &str) -> Result<Refine<str>, regex::Error> {
    let pattern = format!(r"\A(?:{pattern})\z");
    let regex = regex::Regex::new(&pattern)?;
    Ok(refine(move |value| regex.is_match(value)))
}

/// `Refine a` when lift / the caller names `a` (`refine_on::<i32>(|n| …)`).
pub fn refine_on<A: crate::absval::PhotoArg + ?Sized>(
    check: impl Fn(&A) -> bool + Send + Sync + 'static,
) -> Refine<A> {
    Refine::pack(Invariant::Refine(crate::ir::RefineFn::new::<A::Photo>(
        check,
    )))
}

pub fn unique() -> Invariant {
    Invariant::Unique
}

pub fn nested(schema: Schema) -> Invariant {
    Invariant::Nested(Box::new(schema))
}

pub fn shape(form: Form) -> Invariant {
    Invariant::Shape(form)
}

pub fn when(pred: Predicate, then: Invariant) -> Invariant {
    Invariant::When {
        pred,
        then: Box::new(then),
    }
}

pub fn at(pos: usize) -> Invariant {
    Invariant::At(pos)
}

pub fn width(n: usize) -> Invariant {
    Invariant::Width(n)
}

pub fn pred_eq(field: &str, lit: &str) -> Predicate {
    Predicate::Eq {
        field: field.into(),
        lit: lit.into(),
    }
}

pub fn pred_in(field: &str, lits: &[&str]) -> Predicate {
    Predicate::In {
        field: field.into(),
        lits: lits.iter().map(|s| (*s).to_string()).collect(),
    }
}

pub fn pred_not(pred: Predicate) -> Predicate {
    Predicate::Not(Box::new(pred))
}

pub fn pred_defined(field: &str) -> Predicate {
    Predicate::Defined {
        field: field.into(),
    }
}

pub fn rewrite(field: &str, pred: Predicate, then: Invariant) -> Rewrite {
    Rewrite {
        field: field.into(),
        pred,
        then,
    }
}
