# Esa22Copy

A Lean 4 formalization scaffolded by the Tex2Lean extension.

## Build

```sh
lake update            # resolves Mathlib and arlib at the pinned revisions
lake exe cache get     # download Mathlib oleans — do not skip this
lake build
```

Toolchain: `leanprover/lean4:v4.33.0`. Mathlib is pinned to `v4.33.0`;
arlib to `main`.

## What "done" means here

Not "it compiles". Three checks, in increasing order of strength — ship only
when all three agree:

1. `#print axioms <capstone>` reports exactly
   `[propext, Classical.choice, Quot.sound]`. This walks the whole transitive
   dependency tree and is the only authoritative check.
2. `lake build` emits **zero** `declaration uses sorry` warnings. This also
   catches sorries in dead declarations that (1) never reaches.
3. `grep -rn "sorry\|admit\|native_decide\|sorryAx" Esa22Copy/` comes back clean.
   Cheap, necessary, and not sufficient — it is fooled by comments and blind to
   transitive use. On its own it is the classic false "it's proven".

## Audit surface

`Esa22Copy/Model/` holds everything the headline theorem asserts, and nothing
else. `Esa22Copy/Meta/ModelClosure.lean` machine-checks that boundary on every
build.

**It holds no proofs.** Statements and the vocabulary they are stated in live in
`Model/`; the arguments live in `Esa22Copy/Analysis/`, one file per surface file
that states something — `Model/Theorem.lean` is proved in
`Analysis/TheoremProof.lean`. **No name is used on both sides**, so that a file
named anywhere — a tab, a log line, a commit — is one file rather than two. The
headline's own proof in `Model/Theorem.lean` is a line or two assembling lemmas
proved under `Analysis/`. This is what makes the surface worth reading: a
referee can see everything being claimed without reading a tactic.

Before trusting those checks, point them at a constant you know violates the
property and confirm they fail — a check that cannot fail is worse than no
check, because it will be believed.
