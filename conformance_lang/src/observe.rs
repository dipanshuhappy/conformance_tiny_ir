//! Observe = fold of `M`, `M = ValueCtx → ValueCtx` (last write wins).

use crate::absval::AbsVal;
use crate::ir::{Field, Schema, ValueCtx};

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
