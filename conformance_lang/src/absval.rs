//! Abstract values at a site — Known / OneOf / Array / Record / Absent / Unknown.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbsVal {
    Known(String),
    OneOf(BTreeSet<String>),
    /// Observed a sequence (`vec![…]` / `Multiple`), with children.
    Array(Vec<AbsVal>),
    /// Observed a struct (`ErrorMessage { … }`). Names are the inner Schema fields.
    Record(BTreeMap<String, AbsVal>),
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

/// `apply` could not read this photo as `A`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApplyErr {
    Fail(String),
    Undecidable(String),
}

/// How `AbsVal` becomes `A`. Lift picks `A`; `refine(|x|)` is `Fn(&A::Arg)`.
///
/// Photo `Known` is still `String` — other `A`s wait on a richer photo.
pub trait Photo: Sized + 'static {
    type Arg: ?Sized + Send + Sync + 'static;
    fn apply(val: &AbsVal, check: impl Fn(&Self::Arg) -> bool) -> Result<(), ApplyErr>;
}

/// The `x` in `refine(|x|)`. rustc types this from the closure; lift maps field → this.
pub trait PhotoArg: Send + Sync + 'static {
    type Photo: Photo<Arg = Self>;
}

impl PhotoArg for str {
    type Photo = String;
}

impl Photo for String {
    type Arg = str;
    fn apply(val: &AbsVal, check: impl Fn(&str) -> bool) -> Result<(), ApplyErr> {
        match val {
            AbsVal::Known(s) => {
                if check(s) {
                    Ok(())
                } else {
                    Err(ApplyErr::Fail(format!("= {s:?}")))
                }
            }
            AbsVal::Unknown => Err(ApplyErr::Undecidable("value Unknown".into())),
            AbsVal::Absent => Err(ApplyErr::Fail("is absent".into())),
            AbsVal::Array(xs) => apply_str_each(xs, &check),
            AbsVal::Record(_) => Err(ApplyErr::Fail("is a record".into())),
            AbsVal::OneOf(_) => Err(ApplyErr::Undecidable("OneOf, not a single value".into())),
        }
    }
}

fn apply_str_each(xs: &[AbsVal], check: &dyn Fn(&str) -> bool) -> Result<(), ApplyErr> {
    let mut und = None;
    for x in xs {
        match x {
            AbsVal::Known(s) => {
                if !check(s) {
                    return Err(ApplyErr::Fail(format!("= {s:?}")));
                }
            }
            AbsVal::Unknown => {
                und = Some(ApplyErr::Undecidable("value Unknown".into()));
            }
            AbsVal::Array(inner) => match apply_str_each(inner, check) {
                Ok(()) => {}
                Err(ApplyErr::Fail(m)) => return Err(ApplyErr::Fail(m)),
                Err(e) => und = Some(e),
            },
            AbsVal::Absent => return Err(ApplyErr::Fail("is absent".into())),
            AbsVal::Record(_) => return Err(ApplyErr::Fail("is a record".into())),
            AbsVal::OneOf(_) => {
                und = Some(ApplyErr::Undecidable("OneOf, not a single value".into()));
            }
        }
    }
    match und {
        Some(e) => Err(e),
        None => Ok(()),
    }
}
