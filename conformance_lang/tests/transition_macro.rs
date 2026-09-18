//! Generated `#[test]`s from `#[conformance_macros::transition]` run as part of this file.

use conformance_macros::{transition, Schema};

#[allow(dead_code)]
#[derive(Schema)]
struct Msg {
    #[enum_("hi", "bye")]
    kind: String,
    #[required_if(kind = "hi")]
    name: Option<String>,
}

#[allow(dead_code)]
#[transition]
fn for_kind(mut m: Msg) -> Msg {
    if m.kind == "hi" {
        m.name = Some("Ada".into());
        return m;
    }
    helper(m)
}

#[allow(dead_code)]
fn helper(mut m: Msg) -> Msg {
    m.name = None;
    m
}

#[allow(dead_code)]
#[transition]
impl Msg {
    fn for_kind_self(mut self) -> Self {
        if self.kind == "hi" {
            self.name = Some("Ada".into());
            return self;
        }
        self
    }
}
