//! Observe = fold of `M`, `M = ValueCtx → ValueCtx` (last write wins).

use crate::absval::AbsVal;
use crate::ir::{Field, Schema, ValueCtx};

/// A relative, sequential wire observation.
///
/// Fragments compose without knowing where their caller will place them.  The
/// right fragment is shifted by the left fragment's extent; observing the
/// finished fragment seats those relative positions on the wire.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WireFragment {
    extent: usize,
    fields: Vec<(String, usize, usize)>,
}

impl WireFragment {
    /// The identity fragment.
    pub fn empty() -> Self {
        Self::default()
    }

    /// One emitted field occupying `len` wire units.
    pub fn emit(field: impl Into<String>, len: usize) -> Self {
        Self {
            extent: len,
            fields: vec![(field.into(), 0, len)],
        }
    }

    /// Sequential composition. The right fragment begins after the left one.
    pub fn concat(mut self, right: Self) -> Self {
        let shift = self.extent;
        self.fields.extend(
            right
                .fields
                .into_iter()
                .map(|(field, pos, len)| (field, pos + shift, len)),
        );
        self.extent += right.extent;
        self
    }

    pub fn extent(&self) -> usize {
        self.extent
    }

    /// Lower the relative fragment to Tiny's existing absolute wire facts.
    pub fn observe(self, origin: usize) -> ValueCtx {
        self.fields
            .into_iter()
            .fold(ValueCtx::default(), |ctx, (field, pos, len)| {
                ctx.with_wire(&field, origin + pos, len)
            })
    }
}

fn fact_abs(fact: Fact) -> AbsVal {
    match fact {
        Fact::Lit(s) => AbsVal::Known(s),
        Fact::Absent => AbsVal::Absent,
        Fact::Unknown => AbsVal::Unknown,
        Fact::OneOf(vs) => AbsVal::OneOf(vs.into_iter().collect()),
        Fact::Array(xs) => AbsVal::Array(xs.into_iter().map(fact_abs).collect()),
        Fact::Record(m) => {
            AbsVal::Record(m.into_iter().map(|(k, v)| (k, fact_abs(v))).collect())
        }
        Fact::Wire { .. } => AbsVal::Unknown,
    }
}

/// One write into a `ValueCtx`. Unfold, layout, and fingers all emit these.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fact {
    Lit(String),
    Absent,
    Unknown,
    OneOf(Vec<String>),
    Array(Vec<Fact>),
    Record(std::collections::BTreeMap<String, Fact>),
    Wire { pos: usize, len: usize },
}

impl ValueCtx {
    /// Apply one fact. This *is* `M`.
    pub fn put(self, field: &str, fact: Fact) -> Self {
        match fact {
            Fact::Lit(s) => self.lit(field, s),
            Fact::Absent => self.absent(field),
            Fact::Unknown => self.unknown(field),
            Fact::OneOf(vs) => self.one_of(field, vs),
            Fact::Array(xs) => self.array_of(
                field,
                xs.into_iter().map(fact_abs).collect(),
            ),
            Fact::Record(m) => {
                self.record(field, m.into_iter().map(|(k, v)| (k, fact_abs(v))))
            }
            Fact::Wire { pos, len } => self.with_wire(field, pos, len),
        }
    }
}

/// Fold one `Fact` per Schema field. `read` uses `field.locator` (or the
/// Rust name) however the source is seated — layout JSON, live value, test.
pub fn observe(schema: &Schema, mut read: impl FnMut(&Field) -> Fact) -> ValueCtx {
    schema
        .fields
        .iter()
        .fold(ValueCtx::default(), |ctx, f| ctx.put(&f.name, read(f)))
}
