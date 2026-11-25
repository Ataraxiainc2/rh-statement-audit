# Proposal: statement-stability tests for `RiemannHypothesis` in Mathlib

**Status:** draft, not submitted. (Do not open a Mathlib issue/PR without the repository owner's go-ahead.)
**Target:** `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` plus a new test file `MathlibTest/RiemannHypothesisStatement.lean`
(or `Mathlib/NumberTheory/LSeries/RiemannHypothesisEquiv.lean` if reviewers prefer the results in the library).
**Reference implementation:** `RhStatementAudit/Anchors.lean` and `RhStatementAudit/Eta.lean` in this repository.
Compiled against Mathlib tag `v4.33.1` (`0df444a3`); 0 `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. Motivation

On 2026-11-20 a Lean development was released that proves Mathlib's `RiemannHypothesis` with standard axioms.
Independent kernels have since checked it. That moved the question "does the formal statement mean RH?" from
folklore to a load-bearing question. Today the answer rests on:

* a docstring (`A formal statement of the Riemann hypothesis …`);
* reviewers reading a definition whose meaning depends on a chain of about 10 definitions (Hurwitz zeta →
  `WeakFEPair.Λ` → Mellin transform → theta kernels → `Gammaℝ` → `Complex.Gamma`, …) and on junk-value
  conventions (`x/0 = 0`, `Γ(-n) = 0`, `0^s = 0`, `tsum` of non-summable = 0);
* third-party write-ups.

Mathlib already contains every ingredient needed to make the meaning **machine-checked and permanent**.
The point of this proposal is to turn that meaning into *regression tests*. A future refactor of
`riemannZeta`, of `hurwitzZetaEven`, of junk-value conventions, or of the statement itself must then keep
these equivalences, or fail CI loudly.

## 2. Proposed content

All items below are proved in the reference implementation.

### 2.1 Equivalent formulations (the core request)

```lean
/-- Critical-strip form. -/
theorem riemannHypothesis_iff_strip :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- The hypothesis `s ≠ 1` is redundant (the junk value `ζ 1 = (γ - log 4π)/2` is nonzero). -/
theorem riemannHypothesis_iff_no_one :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2

/-- `riemannZeta`-free form: any function analytic on `ℂ \ {1}` given by `∑ n⁻ˢ` on `Re s > 1`. -/
theorem riemannHypothesis_iff_viaContinuation :
    RiemannHypothesis ↔
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f {1}ᶜ →
        (∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (f s)) →
        ∀ s : ℂ, 0 < s.re → s.re < 1 → f s = 0 → s.re = 1 / 2

/-- `riemannZeta`-free form via an explicit, absolutely convergent Dirichlet eta series. -/
theorem riemannHypothesis_iff_viaEta :
    RiemannHypothesis ↔
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        ∑' k : ℕ, (1 / (2 * (k : ℂ) + 1) ^ s - 1 / (2 * (k : ℂ) + 2) ^ s) = 0 → s.re = 1 / 2
```

### 2.2 Supporting lemmas, also useful on their own

```lean
/-- The excluded set is exactly the set of zeros in the closed left half-plane. -/
theorem riemannZeta_eq_zero_iff_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-- Uniqueness of the continuation (characterisation of `riemannZeta` on `ℂ \ {1}`). -/
theorem eqOn_riemannZeta_of_analyticOnNhd_of_hasSum {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {1}ᶜ)
    (hser : ∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (f s)) :
    Set.EqOn f riemannZeta {1}ᶜ

/-- `HasSum` (not only `tsum`) version of `zeta_eq_tsum_one_div_nat_add_one_cpow`. -/
theorem hasSum_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s)

theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12
```

### 2.3 Pure regression tests (`MathlibTest/`, not library API)

```lean
-- The statement, unfolded: any edit to `RiemannHypothesis` must update this test consciously.
example : RiemannHypothesis ↔
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := Iff.rfl
#guard_msgs in #print axioms riemannHypothesis_iff_viaEta  -- expect only the three standard axioms
```

## 3. Why these and not others

| Test | Failure mode it catches |
|---|---|
| `iff_strip` | Wrong excluded set, wrong quantifier structure, `1/2` elaborated in `ℕ`. |
| `iff_no_one` | Junk value at `s = 1` changing meaning (e.g. if a refactor made `ζ 1 = 0`). |
| `riemannZeta_eq_zero_iff_of_re_nonpos` | Trivial-zero set too large or too small. |
| `iff_viaContinuation` | *Any* bug anywhere in the Hurwitz / Mellin / theta / Γ chain (the statement no longer mentions `riemannZeta`). |
| `iff_viaEta` | Same, through an explicit series with no analytic-continuation machinery in the statement. Also documents the `tsum` pitfall: the naive alternating series is not summable in Mathlib's sense on the strip. |
| `hasSum_riemannZeta` | `tsum` junk (non-summable ⇒ 0) masking a wrong identity. |
| `Iff.rfl` snapshot | Silent edits of the definition. |

## 4. Costs

* About 300 lines, `import`-light. Only `LSeries`, `Harmonic.ZetaAsymp`, `Complex.LocallyUniformLimit` and
  `Analytic.Uniqueness` are needed; the reference implementation uses `import Mathlib` only for convenience.
* No new definitions in the library except possibly `riemannZeta`-free predicates if reviewers want them.
  Otherwise the formulations stay inside theorem statements.
* Build time: the reference implementation compiles in about 1 min on a laptop on top of a cached Mathlib.

## 5. Open questions for reviewers

1. Library or `MathlibTest`? The supporting lemmas (§2.2) seem library-worthy. The `Iff.rfl` snapshot is
   test-only.
2. Should the analogous statements for `DirichletCharacter.LFunction` (GRH) be included? They are
   straightforward with the same technique (see C. Toledo's `IsTextbookL`), but they are not done here.
3. Naming: `riemannHypothesis_iff_*` vs `RiemannHypothesis.iff_*`.

## 6. Prior art

* Mathlib already has the ingredients: `zeta_eq_tsum_one_div_nat_add_one_cpow`, `differentiableAt_riemannZeta`,
  `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`, `riemannZeta_one_ne_zero`, and the
  identity-theorem argument in `riemannZeta_conj`.
* C. Toledo, `cert-machine/instruments/alpoge-grh/spec/{Spec,Textbook}.lean`, 2026-11-21: strip form and
  characterisation form at the same pin.
