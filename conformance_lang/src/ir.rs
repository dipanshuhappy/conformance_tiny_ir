//! Core IR — Schema · Field · Invariant · Predicate · Compose · Eval.

use std::collections::{BTreeMap, BTreeSet};

use crate::absval::AbsVal;

/// Parent type under check (`Msg`, `E1`, …).
#[derive(Debug, Clone)]
pub struct Schema {
    pub name: String,
    /// Optional fixed-width record length (TRACS-style).
    pub width: Option<usize>,
    pub fields: Vec<Field>,
}

/// Named slot inside a Schema.
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub locator: Locator,
    pub invariants: Vec<Invariant>,
    /// Optional geometry declared on the field (also expressible as Properties).
    pub wire: Option<WireMeta>,
}

#[derive(Debug, Clone)]
pub struct WireMeta {
    pub pos: Option<usize>,
    pub len: Option<usize>,
}

/// How to find the field on the value / wire.
#[derive(Debug, Clone)]
pub enum Locator {
    Path(String),
    Wire(String),
    Tag(String),
}

impl Locator {
    pub fn key(&self) -> &str {
        match self {
            Locator::Path(s) | Locator::Wire(s) | Locator::Tag(s) => s,
        }
    }
}

/// `(ctx, field) → Pass | Fail` — evaluated as data.
#[derive(Debug, Clone)]
pub enum Invariant {
    /// Value ∈ set (empty string counts as a value; use Defined separately).
    OneOf(Vec<String>),
    /// Field is present (Some / non-empty / emitted).
    Defined,
    /// Field is absent.
    Absent,
    /// Observed form (scalar string vs array).
    Shape(Form),
    /// Geometry: 1-based start.
    At(usize),
    /// Geometry: width in characters.
    Width(usize),
    /// Compose: if Predicate then Invariant else skip.
    When {
        pred: Predicate,
        then: Box<Invariant>,
    },
    /// Compose: all must Pass.
    All(Vec<Invariant>),
    /// Compose: any may Pass.
    Any(Vec<Invariant>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Form {
    Scalar,
    Array,
}

/// `ctx → Bool`
#[derive(Debug, Clone)]
pub enum Predicate {
    Eq { field: String, lit: String },
    In { field: String, lits: Vec<String> },
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
    Not(Box<Predicate>),
}

/// Sugar name for Invariant composition helpers (All / Any / When live on Invariant).
#[derive(Debug, Clone, Copy)]
pub enum Compose {
    All,
    Any,
    When,
}

/// Observed values of one state (after a transition, or a hand-built ctx).
///
/// A missing key is **unobserved**, not Absent. Absent is an explicit fact.
#[derive(Debug, Clone, Default)]
pub struct ValueCtx {
    /// field name → abstract value
    pub values: BTreeMap<String, AbsVal>,
    /// field name → observed wire geometry
    pub wire: BTreeMap<String, WireMeta>,
    /// field name → literals this path has ruled out (`else` of `==` / `matches!`)
    pub excluded: BTreeMap<String, BTreeSet<String>>,
}

impl ValueCtx {
    fn write_value(mut self, field: &str, val: AbsVal) -> Self {
        self.excluded.remove(field);
        self.values.insert(field.into(), val);
        self
    }

    pub fn lit(self, field: &str, value: impl Into<String>) -> Self {
        self.write_value(field, AbsVal::Known(value.into()))
    }

    pub fn absent(self, field: &str) -> Self {
        self.write_value(field, AbsVal::Absent)
    }

    pub fn unknown(self, field: &str) -> Self {
        self.write_value(field, AbsVal::Unknown)
    }

    pub fn array(self, field: &str) -> Self {
        self.write_value(field, AbsVal::Array)
    }

    pub fn one_of(self, field: &str, values: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.write_value(
            field,
            AbsVal::OneOf(values.into_iter().map(|s| s.into()).collect()),
        )
    }

    pub fn with_wire(mut self, field: &str, pos: usize, len: usize) -> Self {
        self.wire.insert(
            field.into(),
            WireMeta {
                pos: Some(pos),
                len: Some(len),
            },
        );
        self
    }

    pub fn exclude(mut self, field: &str, lit: impl Into<String>) -> Self {
        self.excluded
            .entry(field.into())
            .or_default()
            .insert(lit.into());
        self
    }
}
