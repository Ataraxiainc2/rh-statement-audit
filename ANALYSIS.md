# Statement-risk analysis: `RiemannHypothesis` in the Alpöge release

> Proof announced by **Levent Alpöge** (Anthropic; Junior Fellow, Harvard Society of Fellows) on 2026-11-20 at
> <https://alpo.ge/remark.pdf>, written, per the announcement, working with Claude. This report is an
> independent audit of the **statement**, not of the proof, and is not affiliated with the author. It was
> prepared with AI assistance (Claude Code). The Spanish original is [`ANALISIS.md`](ANALISIS.md); this is
> a faithful English version.

**Date:** 2026-11-25 · **Verified environment:** Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (= Mathlib's official tag `v4.33.1`). This is the environment
pinned by the release's `lake-manifest.json`. Its SHA-256 (`fee57ee9…4774`) is identical to the one in the
alpo.ge `lean.tar.gz` archive, per tamnd/riemann-lean's per-file manifest.

Every code quotation below was read from **Mathlib's source at that commit**, not from memory. The local
clone is `.lake/packages/mathlib`, with `HEAD = 0df444a3` and a clean tree. Claims marked **[Lean]** are
proved in `RhStatementAudit/*.lean` and compiled with `lake build` (8710/8710 jobs, locally and in CI). They
use only `propext`, `Classical.choice` and `Quot.sound`.

---

## 0. Verdict

The sentence under analysis:

> "The statement is not the one we think. That is the main residual risk. Mathlib defines RiemannHypothesis
> as: every zero of riemannZeta that is not trivial and with s ≠ 1 has real part 1/2. If that definition or
> the one of riemannZeta had a subtle flaw, something else would have been proved. This risk is low: the
> definition existed and had been reviewed before, and Toledo proved in Lean that it is equivalent to the
> textbook form."

| Part of the claim | Assessment |
|---|---|
| Paraphrase of the definition | **Correct**, with one precision: "not trivial" means exactly "not of the form −2(n+1), n ∈ ℕ". No separate triviality predicate is involved. |
| "A subtle flaw would mean something else was proved" | **Correct.** It is the only failure route left if the kernel is sound and the axioms are the standard ones. |
| "It is the main residual risk" | **Needs qualifying.** Among *semantic* risks, yes. But once anchor theorems like the ones in this repository compile, that risk is **checked mechanically**. The main *practical* residual risk is the **integrity of the trusted environment**: upstream, untouched Mathlib and a trustworthy `.olean` cache. `comparator` **does not cover that, by design** (§6). |
| "The definition existed and had been reviewed" | **Correct and verifiable.** `def RiemannHypothesis` entered Mathlib 4 on 2023-06-29 (port from mathlib3, X. Roblot, #5556). It was rewritten on top of Hurwitz zeta on 2024-05-31 (D. Loeffler, #13273). That is about 2.5 years of public use before the release; the ζ definition chain has had its current form for about 1.5 years. |
| "Toledo proved in Lean that it is equivalent to the textbook form" | **It exists, but I did not compile it.** His files (`cert-machine/instruments/alpoge-grh/spec/{Spec,Textbook}.lean`) state, at the same pin, the strip form and a characterization of ζ that does not use `riemannZeta`. His report leaves two statement checks open: *Comparator* was stopped at 53 h with no verdict, and the planted-error test was "refused". **This repository reproduces those equivalences independently and extends them**: the explicit-η form, the exact set of trivial zeros, and the redundancy of `s ≠ 1`. |
| "This risk is low" | **Right in direction, but the label undersells one thing and misdirects another** (§7). For the *meaning* of the statement the risk is **very low** and now checked in Lean. "Low" suggests the remaining risk sits in the definition; it actually sits in the **environment**: Mathlib pin, cache, toolchain. |

---

## 1. Exact definition and definition chain (source, commit `0df444a3`)

### 1.1 `RiemannHypothesis` — `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:183-186`

```lean
/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
@[wikidata Q205966]
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

* The anonymous binders `(_ : P)` are implications. `n + 1` elaborates as `(↑n + 1 : ℂ)`.
* `1 / 2` elaborates in `ℝ`, because `s.re : ℝ`, so it means 0.5 and not natural-number division (`1/2 = 0`).
* **[Lean]** `riemannHypothesis_unfold` shows by `Iff.rfl` that the definition matches, character for
  character, the release's `RiemannZetaZerosOnLine` (in `Statements.lean`). The release's `Main.lean` also
  closes both `riemannHypothesis` and `riemannZeta_eq_zero_re` with the same term `rhOfAll`, which confirms
  the definitional equality.

### 1.2 `riemannZeta` and its chain

| Constant | Definition (file:line) |
|---|---|
| `riemannZeta` | `def riemannZeta := hurwitzZetaEven 0` — `RiemannZeta.lean:121` |
| `hurwitzZetaEven a` | `Function.update (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s) 0 (if a = 0 then -1 / 2 else 0)` — `HurwitzZetaEven.lean:583-585` |
| `completedHurwitzZetaEven a s` | `((hurwitzEvenFEPair a).Λ (s / 2)) / 2` — `HurwitzZetaEven.lean:297` |
| `hurwitzEvenFEPair a : WeakFEPair ℂ` | `f := ofReal ∘ evenKernel a`, `g := ofReal ∘ cosKernel a`, `k := 1/2`, `ε := 1`, `f₀ := if a = 0 then 1 else 0`, `g₀ := 1` — `HurwitzZetaEven.lean:254-272` |
| `WeakFEPair.Λ s` | `P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀` — `AbstractFuncEq.lean:379` |
| `WeakFEPair.Λ₀` | `mellin P.f_modif` — `AbstractFuncEq.lean:376`. `f_modif` subtracts from `f` its asymptotics at 0 and ∞ (`:247`). |
| `mellin f s` | `∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t` — `Analysis/MellinTransform.lean` |
| `evenKernel a x` | lift to `UnitAddCircle` of `ξ ↦ rexp (-π ξ² x) · re (jacobiTheta₂ (ξ I x) (I x))` (`@[irreducible]`) — `HurwitzZetaEven.lean:63-75` |
| `jacobiTheta₂ z τ` | `∑' n : ℤ, cexp (2π i n z + π i n² τ)` — `JacobiTheta/TwoVariable.lean:45,251` |
| `Gammaℝ s` | `π ^ (-s / 2) * Gamma (s / 2)` — `Gamma/Deligne.lean:43` |
| `Complex.Gamma s` | `GammaAux ⌊1 - s.re⌋₊ s` (Euler integral plus recurrence; `@[irreducible]`) — `Gamma/Basic.lean:287` |
| `cpow` | `x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y)` — `Pow/Complex.lean:35` |

This is Riemann's classical construction via θ and the Mellin transform: Λ(s) = π^{-s/2} Γ(s/2) ζ(s). The
poles of Λ at 0 and 1 are removed explicitly via `f₀` and `g₀`.

---

## 2. Junk values

Mathlib makes partial functions total: `x / 0 = 0`, `Γ(−n) = 0` (`Complex.Gamma_neg_nat_eq_zero`,
`Gamma/Basic.lean:344`), and the `tsum` of a non-summable family is `0`. There are three places where a
convention could create or erase zeros.

### 2.1 `s = 1` (the pole)
* The value the definition gives at `s = 1` is `ζ(1) = (γ − log 4π)/2` (`riemannZeta_one`,
  `ZetaAsymp.lean:418`). It is nonzero (`riemannZeta_one_ne_zero`, `:441`).
* Consequence: the hypothesis `s ≠ 1` in `RiemannHypothesis` is **redundant**. It neither weakens nor
  strengthens the statement. **[Lean]** `riemannHypothesis_iff_no_one`.

### 2.2 `s = 0` (an explicit patch)
* `Γℝ(0) = Γ(0) = 0`, so `Λ(0)/Γℝ(0)` would be the junk value `0`. That is why `hurwitzZetaEven`
  **patches** the value at 0 with `Function.update … 0 (-1/2)`.
* Is the patch right? Yes, and we do not have to trust it. `differentiableAt_riemannZeta` (for every
  `s ≠ 1`) implies continuity at 0. A wrong patched value would make ζ discontinuous at 0, and that theorem
  would not compile. **[Lean]** `anchor_zeta_zero : riemannZeta 0 = -1/2`.

### 2.3 Trivial zeros `s = −2(n+1)` (a "lucky" division by zero)
* Here `Γℝ(−2(n+1)) = π^{n+1} Γ(−(n+1)) = 0` in Mathlib. So **the value of `riemannZeta` at the trivial
  zeros literally comes from `Λ(s)/0 = 0`**: a division by zero that happens to match the true value.
* That is not a problem. Again, differentiability at every `s ≠ 1` forces the value to be the limit, which is
  the true zero (Λ finite, Γℝ with a pole).
* **General lesson:** any wrong point value in `ℂ \ {1}` is ruled out by `differentiableOn_riemannZeta`. So the
  analyticity anchor is not decorative. It kills the failure modes of the form "junk value at an isolated
  point", for example a hypothetical spurious 0 at ½ + 14.13 i or off the line.

### 2.4 `tsum` and the Dirichlet series
* `zeta_eq_tsum_one_div_nat_cpow` is an equality of `tsum`s. On its own it could be "true by junk" if the
  series were not summable. **[Lean]** `anchor_hasSum_dirichlet` strengthens it to `HasSum`, i.e. genuine
  unconditional convergence, for `Re s > 1`.
* For Dirichlet's η this is critical (§5). The alternating series converges only **conditionally** on
  `0 < Re s ≤ 1`, so `∑' n, (-1)^n/(n+1)^s` **is 0 on the whole critical strip**. A naive "RH via η" written
  with `tsum` would be a false statement about junk. That is why we use the paired form, which converges
  absolutely.

---

## 3. Trivial zeros: is exactly the right set excluded?

The excluded set is `T = {−2(n+1) : n ∈ ℕ} = {−2, −4, −6, …}`.

* Excluding **too much** would weaken RH, e.g. with `ℤ` instead of `ℕ`, or with truncated subtraction in `ℕ`.
* Excluding **too little** would make RH false, since trivial zeros have Re ≠ ½. A "proof" would then
  indicate an inconsistency.
* **[Lean]** `anchor_trivial_zeros_exact`: on `Re s ≤ 0`, `ζ(s) = 0 ↔ s ∈ T`, exactly. The proof
  (`riemannZeta_ne_zero_of_re_nonpos`) uses:
  * the functional equation `riemannZeta_one_sub`;
  * non-vanishing on `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`);
  * `Γ ≠ 0`.

  So only cos(πw/2) can vanish. That gives odd integers, i.e. `s ∈ −2ℕ`. The case `s = 0` is excluded
  because `ζ(0) = −½`.
* Note: `riemannZeta_ne_zero_of_one_le_re` (`Nonvanishing.lean:411`) does **not** require `s ≠ 1`, precisely
  because the junk value at 1 is nonzero. Its docstring says so explicitly.

---

## 4. The `cpow` convention

`x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y)`, with the principal `log`
(arg ∈ (−π, π]).

* For `x = n > 0` real, `log n ∈ ℝ`, so `n^s = e^{s log n}`: the standard convention. There is no branch
  ambiguity in the series.
* The only junk is `0^s = 0` (for `s ≠ 0`). In `∑_{n≥0} 1/n^s` the term `n = 0` is `1/0 = 0`: harmless.
  Mathlib also provides the `n + 1` form (`zeta_eq_tsum_one_div_nat_add_one_cpow`, whose docstring says
  "to avoid relying on mathlib's conventions for `0 ^ s`"). Our anchors use the `n + 1` form.
* **[Lean]** `cpow_convention` pins the definition by `rfl`. If it changed upstream, the anchor would fail.

---

## 5. Which lemma rules out which failure mode

| Hypothetical failure mode | Effect | Ruled out by |
|---|---|---|
| `riemannZeta` is not ζ on `Re s > 1` | RH proved for another function | `zeta_eq_tsum_one_div_nat_cpow` / **[Lean]** `anchor_hasSum_dirichlet` (with `HasSum`), `riemannZeta_two = π²/6` |
| A "wrong" continuation (another function agreeing on Re > 1) | RH about another function | `differentiableAt_riemannZeta` (s ≠ 1) + identity theorem: **[Lean]** `anchor_unique` (any `f` analytic on `ℂ\{1}` with that series equals `riemannZeta`) |
| Junk value at an isolated point (patches, `x/0`) | spurious or erased zero | differentiability at every `s ≠ 1` (§2.2–2.3); **[Lean]** `anchor_zeta_zero`, `anchor_zeta_neg_one = −1/12` |
| Junk at `s = 1` | RH false or vacuous depending on the value | `riemannZeta_one_ne_zero`; **[Lean]** `riemannHypothesis_iff_no_one` |
| Trivial-zero set miswritten | RH weakened or false | `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`; **[Lean]** `anchor_trivial_zeros_exact` |
| `1/2` elaborated in `ℕ` (= 0) | RH would say "Re s = 0" | elaboration in `ℝ` (the type of `s.re`); **[Lean]** the strip-form and η equivalences would be impossible with Re = 0 |
| Wrongly nested quantifiers or hypotheses | a different statement | **[Lean]** `riemannHypothesis_unfold` (`Iff.rfl`), `riemannHypothesis_iff_strip` |
| The whole Hurwitz/Mellin/θ chain is wrong | RH about another function | **[Lean]** `riemannHypothesis_iff_viaContinuation` and `riemannHypothesis_iff_viaEta`: RH ⇔ statements in which **`riemannZeta` does not occur** |
| Wrong functional equation | ζ not symmetric | `riemannZeta_one_sub`, `completedRiemannZeta_one_sub` (Λ(1−s) = Λ(s)) |

**What the anchors do not cover:**
* The basic notions they rely on (`HasSum`, `cpow` on positive reals, `AnalyticOnNhd`, `re`, `ℂ`). A bug
  there would be a "deep" Mathlib bug affecting almost everything.
* The release's **Dirichlet L-function statements** (`DirichletLNonvanishingRightOfHalf`,
  `DirichletLZerosOnLine`, …). For those, Toledo's `Textbook.lean` states an analogous characterization
  (`IsTextbookL`), which I have not compiled.

---

## 6. What `comparator` does and does not guarantee

Read from the code of `leanprover/comparator` (`Comparator/Compare.lean`) and its README.

**It guarantees**, under its assumptions, for each theorem in `theorem_names`:
1. The **statement** (name, type, universe levels) is identical in Challenge and Solution.
2. **It does compare dependencies transitively.** `compareAt` puts every constant used in the theorem's type
   on a worklist. `loop` requires each one to have an **identical** `ConstantInfo`
   (`challengeConst != solutionConst → throw`), i.e. the type **and body** of definitions, and recursively
   adds their constants (`runForUsedConsts`). So a homonymous redefinition of `riemannZeta`,
   `hurwitzZetaEven`, etc. **inside the Solution environment** does not pass.
3. The proof uses only `permitted_axioms` and is accepted by the kernel, plus optional external kernels
   (nanoda, con-leche, …).

**It does not guarantee:**
* **That the shared environment is the right one.** Its assumption 1 reads: *"The transitive closure of
  imports of `Challenge.lean` as well as `lakefile.toml`/`lakefile.lean` are controlled by you or
  trustworthy."* Challenge and Solution are built from **the same packages** in the lakefile. If it pinned a
  Mathlib **fork**, the Challenge would be compiled against the fork, the comparison would be fork against
  fork, and it **would pass**. The same holds for a tampered `.olean` cache (README: *"acceptable … if you
  trust the cache"*).
* **That the Challenge's statement means what we think.** That is exactly what the anchors are for.
* On the report that "the build step was stubbed": I could not verify it. If the build is replaced by a
  prebuilt `.lake`, the README allows that only if it was obtained "without compromising your checking
  environment". The guarantee then depends on where the `.olean` files came from.
* **A version detail worth clarifying:** per its README, `comparator` was merged into core as
  `lake comparator` in Lean **v4.35.0**. The release uses **v4.33.1**, so runs on the release must have used
  the standalone `comparator`, or a newer `lake` driving an older toolchain. Each report should say which
  binary and version it used.

**How this repository closes the environment gap** (`scripts/check_pin.py`, run in CI):
* `lean-toolchain` is `v4.33.1`.
* All 9 manifest packages (name, URL, rev) are identical to the release's, and the manifest's SHA-256 matches
  the original archive.
* Mathlib's URL is upstream `leanprover-community/mathlib4`.
* The pinned commit is Mathlib's **official tag `v4.33.1`**. Relative to `master` it adds a single commit that
  touches **only `lean-toolchain`** ("chore: bump toolchain to v4.33.1", merge-base `db584cd6`). Note: it is
  **not an ancestor of `master`** (the GitHub API returns `diverged`). That is normal for Mathlib's version
  tags, but a naive "is it on master?" check fails, as the first version of my script did.
* The local Mathlib checkout is at that commit with **no modifications** (`git status --porcelain` empty), and
  the source text of `def RiemannHypothesis` is the expected one.

---

## 7. Is "low" the right rating?

**My rating:**

1. **Risk that the formal statement does not mean RH: very low, and checked in Lean.** In the pinned
   environment, `RiemannHypothesis` is equivalent, with a compiled proof and standard axioms, to:
   * the strip form `∀ s, 0 < Re s < 1 → ζ(s) = 0 → Re s = ½`;
   * the form without `s ≠ 1`;
   * a form **without `riemannZeta`**: for every `f` analytic on `ℂ\{1}` with `f(s) = ∑ (n+1)^{-s}`
     (`HasSum`) on `Re s > 1`, its zeros in the strip lie on the line;
   * a form **without `riemannZeta`** using Dirichlet's η as an explicit, absolutely convergent series.

   What remains is the correctness of the kernel (mitigated by nanoda and con-leche) and of Mathlib's basic
   notions.
2. **Environment risk (fork, cache, toolchain): low, but it is the one that actually remains, and
   `comparator` does not cover it.** For the release, the pin points at upstream tag `v4.33.1` (verified),
   so the fork risk is closed. The **cache** risk is not fully closed: whoever uses `lake exe cache get`
   trusts Mathlib's cached `.olean` files. Rebuilding Mathlib from source (the CI's `from_source` option) or
   replaying from an export with an external kernel closes it.
3. **Risk of homonyms in untrusted imports:** closed for the statement by the transitive comparison in
   `comparator` and con-leche. Also, the release's `Challenge.lean` and `Statements.lean` import **only**
   `Mathlib`. The static scanner (`scripts/scan_release.py`) finds no homonymous declarations of the
   statement's constants (§8).

**Conclusion:** "low" is right in direction, but the original sentence mixes two things:
* the **semantic** risk, which no longer needs estimating because it has been checked mechanically;
* the **operational** risk (provenance of the environment), which is the real residual and which the
  original sentence does not mention.

Suggested wording:

> "The formal statement is the right one: in Mathlib `v4.33.1` it is proved in Lean, with standard axioms,
> that `RiemannHypothesis` is equivalent to the strip form and to two forms that do not mention
> `riemannZeta`. What remains is trust in the kernel and in the environment: unmodified upstream Mathlib and a
> trustworthy cache. `comparator` assumes that environment rather than checking it, so it must be audited
> separately."

---

## 8. Static scan of the release

`python3 -I scripts/scan_release.py <release>/lean` on the `tamnd/riemann-lean` mirror. It is a byte-exact
mirror of the alpo.ge archive, with a per-file SHA-256 manifest. The three key files (`Statements.lean`,
`Main.lean`, `lake-manifest.json`) match the original archive's hashes.

Local run on 2026-11-25, reading from the mirror's git object store at commit `54f24d40`: **175,187 `.lean`
files scanned in 48 s, RESULT: PASS**. The CI run on GitHub (Linux) gives the same result. Full output is in
`reference/scan_release_result.txt`.

| Check | Result |
|---|---|
| Declarations whose name is **exactly** a statement constant (`RiemannHypothesis`, `riemannZeta`, `HurwitzZeta.hurwitzZetaEven`, `…completedHurwitzZetaEven`, `Gammaℝ`, `DirichletCharacter.LFunction`), `_root_.…`, or inside `namespace DirichletCharacter`/`HurwitzZeta` | **0** |
| `debug.skipKernelTC` / `skipKernelTypeCheck` | **0** |
| `axiom` declarations | **0** |
| `unsafe`, `@[implemented_by]`, `@[extern]` | **0** |
| `Statements.lean` imports only `Mathlib` | yes |
| git sources in `lakefile.toml` | only `https://github.com/leanprover-community/mathlib4` |
| Homonyms in *other* namespaces (soft) | 2: `GodementJacquet.LFunction`, `HeckeCharacter.LFunction`. No effect: the statement uses the fully qualified `DirichletCharacter.LFunction`, which the transitive comparison of comparator/con-leche pins down. |
| `export` (soft) | 38, none of statement constants (internal names, e.g. `f3`, `Kpp`, `exists_meas`) |
| `run_cmd` (soft) | 5, all in `BuildAid/D1–D5.lean`, of the form `Lean.modifyEnv … LibrarySuggestions.nameDenyListExt.addEntry …`. They only affect tactic suggestions, not declarations. |
| `elab` (soft) | 4: internal tactics (`kexactB`, `kcopy`) and a command that copies declarations. Whatever they produce goes through the kernel, and replays from the export (leanchecker, nanoda, con-leche) re-check it. They can fail, but cannot introduce false proofs. |

Process note: the first scan attempt **was not valid**. The Windows checkout failed on paths that were too
long and extracted only 626 files. The first version of the regex also gave false positives on
`Gammaℝ_conj`, because `\b` does not work after `ℝ`. Both are fixed in the version of the script in the
repository.

The scan is **heuristic** (regular expressions over source). It does not replace the transitive comparison
of `comparator` or con-leche, which works on the elaborated environment.

---

## 9. Sources

* Mathlib `0df444a3` (tag `v4.33.1`): `Mathlib/NumberTheory/LSeries/{RiemannZeta,HurwitzZetaEven,AbstractFuncEq,Nonvanishing}.lean`, `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`, `Mathlib/Analysis/SpecialFunctions/{Gamma/Basic,Gamma/Deligne,Pow/Complex}.lean`, `Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`, `Mathlib/Analysis/MellinTransform.lean`.
* Release mirrors: [the-omega-institute/riemann-hypothesis](https://github.com/the-omega-institute/riemann-hypothesis), [CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean), [tamnd/riemann-lean](https://github.com/tamnd/riemann-lean) (per-file hashes); [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) (`main` already uses `v4.37.0-rc1`; it is **not** the original pin).
* `comparator`: [leanprover/comparator](https://github.com/leanprover/comparator) (`README.md`, `Comparator/Compare.lean`).
* Toledo: [report](https://carlostoledo.co/reports/alpoge-grh.html), [Spec.lean](https://github.com/carlostoledo1891/cert-machine/blob/main/instruments/alpoge-grh/spec/Spec.lean), [Textbook.lean](https://github.com/carlostoledo1891/cert-machine/blob/main/instruments/alpoge-grh/spec/Textbook.lean).
* Verification status: [nasqret/riemann-rev](https://github.com/nasqret/riemann-rev).
