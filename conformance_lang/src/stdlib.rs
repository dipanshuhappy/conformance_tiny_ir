//! Stdlib invariants — not new primitives.

use crate::ir::{Form, Invariant, Predicate};

pub fn one_of(values: &[&str]) -> Invariant {
    Invariant::OneOf(values.iter().map(|s| (*s).to_string()).collect())
}

pub fn defined() -> Invariant {
    Invariant::Defined
}

pub fn absent() -> Invariant {
    Invariant::Absent
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
