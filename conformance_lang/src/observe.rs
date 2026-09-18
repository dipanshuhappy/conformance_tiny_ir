//! Observe = fold of `M`, `M = ValueCtx → ValueCtx` (last write wins).

use crate::ir::{Field, Schema, ValueCtx};

/// One write into a `ValueCtx`. Unfold, layout, and fingers all emit these.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fact {
    Lit(String),
    Absent,
    Unknown,
    OneOf(Vec<String>),
    Array,
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
            Fact::Array => self.array(field),
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
