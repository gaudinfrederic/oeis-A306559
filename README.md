# A306559 - self-describing English-words sequence identified with its morphic fixed point, in Lean 4

[![CI](https://github.com/USERNAME/a306559-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/USERNAME/a306559-lean/actions/workflows/ci.yml)

Machine-checked formalization of
[OEIS A306559](https://oeis.org/A306559): *"A self-describing
sequence mostly made of 1's and 0's emerging when written in
English words"* (Eric Angelini and Jean-Marc Falcoz, 2019).
The rule: *"We start with 1, 2, 3. From this point on, the
sequence is extended by the rule that when written in
English words, the lengths of runs of consonants between
successive vowels is the sequence itself."* This repository
proves that such a sequence exists, is unique, and equals
`[1,2,3]` concatenated with the morphic word
`0.W(0).W^2(0).W^3(0)...` of the on-entry conjecture
(`W : 0 -> 11, 1 -> 01`, Charlie Neder, 2019).

## Theorem

```lean
abbrev conjectureEX306559 : Prop :=
  ∀ k : ℕ, run306559 aStar306559 k = (aStar306559 k).val

abbrev conjectureUN306559 : Prop :=
  ∀ a : ℕ → Fin 4, a 0 = 1 → a 1 = 2 → a 2 = 3 →
    (∀ k : ℕ, run306559 a k = (a k).val) → a = aStar306559

theorem A306559 : conjectureEX306559 ∧ conjectureUN306559
```

The sequence `a : ℕ → Fin 4` spells `ZERO`, `ONE`, `TWO`,
`THREE`; `wordOf306559` is the infinite concatenation of
the English names over the 8-letter alphabet;
`vpos306559 a k` is the position of the `(k+1)`-th vowel
(`{E,O}`, the exact vowel set of the finite lexicon) and
`run306559 a k = vpos(k+1) - vpos(k) - 1` counts the
consonants strictly between successive vowels of the whole
word, including runs across a word boundary. The candidate
`aStar306559 = [1,2,3] ++ M306559`, where `M306559 n` is an
MSB-to-LSB fold of `W` over the bits of `n+1`; its morphism
equations `M(2k+1) = (W(M k))[0]` and
`M(2k+2) = (W(M k))[1]` are proved theorems.

## Proof structure

- `vpos_pair306559`: in the morphic zone each block
  `name(M j)` contributes exactly two vowels; the vowel
  positions `vpos(5+2j)`, `vpos(6+2j)` are tracked
  blockwise by induction.
- `run_pair306559`: the two runs produced by block `j+3`
  are exactly `(W(M j))[0]` (internal run `1`) and
  `(W(M j))[1]` (boundary run `1 - M(j+1)`) - each morphic
  name emits its `W`-image pair.
- `aStar306559_selfdesc` (EX): `k <= 4` by kernel
  `decide`, `k >= 5` by the pair lemma - the candidate is
  a fixed point of the describing equation.
- `vpos_congr306559` + `aStar306559_unique` (UN): strong
  induction (`Nat.strongRecOn`); the vowels scrutinizing
  `run(k)` stay inside blocks `0..k-1`, so each term is
  forced by the terms already fixed.
- `Spec_A306559.lean`: frozen verbatim spec
  (`SpecPropA306559 = SpecPropEX ∧ SpecPropUN`, zero
  tactics); `Check_Spec_A306559.lean` closes every
  spec-to-root bridge and transports the theorem:
  `proven_A306559 : SpecPropA306559`.
- `Check_AntiVacuite_A306559.lean`: the full hypothesis
  conjunction of UN is satisfied by `aStar`; `decide`
  anchors `M(0..8)`, `aStar(0..10)`, `vpos(0..6)`,
  `run(0..6)`; charged ablation `aBad306559` (a `ONE`
  instead of `ZERO` at block 3) breaks the equation
  already at `k = 4`.

## What is NOT claimed

- The on-entry conjectured density `2/3` of `ONE`s: open,
  documented, outside the spec.
- The observed coincidence with A039982: Neder's informal
  OEIS note (Mar 04 2019) proves the equivalence between
  the morphic form and that coincidence - it is cited as
  prior work, not re-proved here.
- Any property beyond existence and uniqueness of the
  self-describing fixed point.

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `import Mathlib` only - no project dependencies
- `lake build` - 5 modules, **zero `sorry`**, zero
  `native_decide`, zero `admit`
- `#print axioms` audited exhaustively on 132 declarations
  by `AxiomsReport_A306559.lean` - certified output
  `[propext, Classical.choice, Quot.sound]`, the three
  standard axioms only (kernel-pure chain, remote build
  run 42483487555, `LEAN_EXIT=0`).

## Contents

- `A306559.lean` - the complete self-contained
  development (949 lines): alphabet, English names,
  infinite word by block/offset iterator, vowel positions,
  consonant runs, the morphic candidate and its morphism
  equations, the existence proof (EX), the uniqueness
  proof (UN), and `theorem A306559`.
- `Spec_A306559.lean` - frozen spec layer (Option B,
  verbatim bodies), `SpecPropEX`/`SpecPropUN`/
  `SpecPropA306559`.
- `Check_Spec_A306559.lean` - spec-to-root bridges and
  `proven_A306559 : SpecPropA306559`.
- `Check_AntiVacuite_A306559.lean` - anti-vacuity
  witnesses, kernel anchors, charged ablation.
- `AxiomsReport_A306559.lean` - `#print axioms` on all
  132 audited declarations.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` -
  pinned build configuration.
- `LICENSE` - Apache 2.0.

## Reproduce

```bash
lake exe cache get   # pinned mathlib oleans
lake build           # all 5 modules
# or check single files:
lake env lean A306559.lean
lake env lean Check_Spec_A306559.lean
```

Expected `#print axioms` output on the capstone
(auditable via `lake env lean AxiomsReport_A306559.lean`):

```
'A306559' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Developed under the DemosMathNT program (multi-session
OEIS conjecture formalization effort). The OEIS statement
was submitted verbatim to independent oracles before
formalization (unanimous fidelity verdicts on the spec).
An adversarial oracle pass on the finished theorem was
not unanimous (two `FAUX` verdicts out of six); every
objection was investigated point by point and resolved
against the formal artifact - mistranslations of the
prose prompt or factually false claims (documented in
`VERIFICATIONS/e4-investigation.md` of the source
package). Oracle verdicts are advisory only: correctness
is established by Lean. The morphic-form conjecture is
stated on the OEIS entry; Neder's equivalence with the
tail of A039982 is cited, not re-proved. No first-proof
or new-result claim is made beyond the machine-checked
verification itself.
