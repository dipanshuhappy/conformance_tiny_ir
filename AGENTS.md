# Agents

This repo is the conformance **language**, not Ampere and not recon.

**REQUIRED:** Read `.cursor/skills/tiny-ir-work/SKILL.md` **before** any code or DESIGN change, and **again after** the change before you say it is done. Both gates. The law is [DESIGN.md](DESIGN.md).

- Discuss is the default. Code only after they lock the law and say implement / go / do it.
- `stop` / `revert` / `don't code` / `think` → no leftover edits.
- Fail only Known-illegal. Unobserved ≠ Absent. Unknown ≠ Fail.
- Sugar writes Schema. Do not add a primitive for a name.
- Do not rewrite Ampere or recon runtime so Unfold can see a write.
- Do not commit unless they ask.
