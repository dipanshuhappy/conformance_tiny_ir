//! Abstract values at a site — Known / OneOf / Array / Absent / Unknown.

use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbsVal {
    Known(String),
    OneOf(BTreeSet<String>),
    /// Observed a sequence (`vec![…]`), not a scalar string.
    Array,
    /// Explicitly missing (None / not emitted).
    Absent,
    /// Dynamic — compile-time check cannot decide.
    Unknown,
}

impl AbsVal {
    pub fn known(s: impl Into<String>) -> Self {
        AbsVal::Known(s.into())
    }
}
