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

pub use absval::{AbsVal, ApplyErr, Photo, PhotoArg};
pub use check::{
    eval_rewrite, eval_rewrites, eval_schema, CheckReport, Finding, FindingKind, Skip,
};
pub use ir::{
    Compose, Field, Form, Invariant, Locator, Predicate, Refine, RefineFn, Rewrite, Schema,
    ValueCtx, WireMeta,
};
pub use observe::{observe, Fact, WireFragment};
pub use stdlib::{
    absent, all, at, defined, matches, nested, one_of, or_absent, pred_defined, pred_eq, pred_in,
    pred_not, refine, refine_on, rewrite, shape, unique, when, width,
};
pub use unfold::{eval_crate, eval_tree, eval_unfold, eval_unfold_named, unfold, Observation};

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
        rewrites: vec![],
    }
}
