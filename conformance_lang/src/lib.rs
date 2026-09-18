//! Tiny conformance IR.
//!
//! Primitives: **Schema · Field · Invariant · Predicate · Compose · Eval**
//!
//! Observe fills a `ValueCtx`. Eval scores it. Unfold is one Observe backend.

mod absval;
mod check;
mod ir;
mod observe;
mod stdlib;
mod unfold;

pub use absval::AbsVal;
pub use check::{eval_schema, CheckReport, Finding, FindingKind};
pub use ir::{Compose, Field, Form, Invariant, Locator, Predicate, Schema, ValueCtx, WireMeta};
pub use observe::{observe, Fact};
pub use stdlib::{absent, at, defined, one_of, pred_eq, pred_in, shape, when, width};
pub use unfold::{eval_unfold, eval_unfold_named, unfold, Observation};

/// Convenience: Msg toy schema used in README / tests.
pub fn msg_toy_schema() -> Schema {
    Schema {
        name: "Msg".into(),
        width: None,
        fields: vec![
            Field {
                name: "kind".into(),
                locator: Locator::Path("kind".into()),
                invariants: vec![one_of(&["hi", "bye"])],
                wire: None,
            },
            Field {
                name: "name".into(),
                locator: Locator::Path("name".into()),
                invariants: vec![when(pred_eq("kind", "hi"), defined())],
                wire: None,
            },
        ],
    }
}
