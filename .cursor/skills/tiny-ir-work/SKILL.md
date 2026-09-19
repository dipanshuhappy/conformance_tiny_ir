---
name: tiny-ir-work
description: Use when changing this repo (code, DESIGN, IR, macros, tests), when deciding whether to implement after a discussion, when a change is about to land or just landed, or when the user says think / don't code / stop / revert / implement / beauty / primitives / Ampere / recon.
---

# Tiny IR work

This repo is the **language**. Ampere and recon are consumers. The law is [DESIGN.md](../../../DESIGN.md).

**Read this skill before any code or DESIGN edit. Read it again after the edit, before claiming done.** Skipping either gate is skipping the skill.

## Before (no edit yet)

1. Read DESIGN.md. Name the **law** this change writes. No law → do not code.
2. Sugar or kernel? Sugar writes Schema. Kernel is Schema · Observe · Eval only. No new primitive for a name (`uuid`, `step`, `phase`, `camera`, `forAll`).
3. Did they say **implement / go / do it** after the law was locked?  
   `think` / `don't code` / `what would` / `how do you write` → answer only.  
   `stop` / `revert` → revert now; do not keep a leftover.
4. One example first (hi/bye or one RReq field). Then the change.
5. What test goes **red** on the illegal tuple? If it cannot go red, it is not a test.

## After (edit exists, not done)

1. Re-read this skill and DESIGN.md. If DESIGN **Next** still lists what you just shipped, fix DESIGN.
2. Fail only **Known-illegal**. Unobserved ≠ Absent. Unknown ≠ Fail.
3. Did Ampere / recon **runtime** get rewritten so Unfold can see it? Revert unless they asked.
4. Hidden items, per-name kernel arms, visitor sprawl, a second checker → revert.
5. Run the tests. The illegal case must fail for the **named** reason.
6. Beauty: would they accept this as the law? If it is only more cases in the walker, it is not done.

## How they solve

- **Primitives first.** Ask what the thing *is* (photo vs rewrite, sit vs move, Observe vs Eval). Kill a name that is not a law.
- **Same photo.** `when(P, I)` narrows the ending picture. `rewrite` is the only old/new, scored at `=`.
- **Lift over attrs.** Default walk a Schema struct. `#[leaf]` opts out. Sums are Refine, not nested Schema. Do not invent `#[nested]` as the product.
- **Domain stays in the consumer.** `refine(|x|)` / `fn eci() -> Refine<str>`. This crate does not own uuid/eci/regex.
- **Honest leftovers.** Do not list a closed hole as unsolved. Do not “fix” Unfold-undecidable IDs by pretending `String::new` is a photo.
- **Do not make the consumer prettier for the walker.** `map(for_protocol)` may stay Unknown. Photo is filled by live / fingers.
- **Rename when the name is the bug** (`forAll` → eval). Remove the old name from code *and* plan.
- **Recon plugin is this algebra**, not a second language. Layout JSON and `compute_field` are Observe backends. `enforce_layout!` is a driver, like `#[derive(Schema)]`. See DESIGN “Recon plugin”.

## How they code

- Tiny IR. Compose existing arms (`when`, `one_of`, `shape`, `nested`, `rewrite`).
- Checker never special-cases attrs.
- Path-split; do not union `if` arms.
- `#[except("why")]` / recon `#[accepted]` need a reason. Silence is not a waiver.
- Commit only when they ask.

## Excuses

| Excuse | Reality |
|--------|---------|
| “Just a small helper while we talk” | That is coding. Revert. |
| “Ampere will not compile unless we rewrite map” | Unknown is legal. Do not touch their `=` . |
| “Unobserved should Fail or the test is weak” | Unobserved is Undecidable. Fill the photo or leave it. |
| “I’ll update DESIGN later” | After-gate failed. DESIGN now. |
| “One more AbsVal / Invariant arm for this name” | Domain refine or consumer `fn`. Not kernel. |
| “The walk needs another peel” | Field-follow is the law of `=`. Depth 8. Then Unknown. |
| “Plugin checks are a different system” | Same Schema · Observe · Eval. Different backends. |

## Red flags — stop

- Coding during `think` / `don't code`
- `step` / `phase` / `forAll` / rustc `typeof` as *P*
- Fail on Unknown or missing key
- Kernel `uuid` / `regex` / `chars`
- DESIGN Next lists nested walk, list `one_of`, unique, refine, field-follow as future
- A green test that never saw the illegal literal
