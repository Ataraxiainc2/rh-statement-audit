/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Statement anchors for Mathlib's `RiemannHypothesis`

Pinned to Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` / Lean `v4.33.1`, i.e. the exact
environment of the 2026-11-20 Alpöge release.

The purpose of this file is *not* to prove anything new about ζ.  It proves, with no `sorry` and
only the standard axioms, a set of theorems that pin down what the proposition
`RiemannHypothesis` (as defined in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) actually
says.  If any of the definitions in the chain
`RiemannHypothesis → riemannZeta → hurwitzZetaEven → completedHurwitzZetaEven → WeakFEPair.Λ →
mellin → evenKernel → jacobiTheta₂ …` were subtly wrong (wrong function, wrong set of excluded
zeros, junk-value accident, `cpow` convention accident), at least one of these theorems would
fail to compile.
-/
import Mathlib

open Complex Filter Topology Set
open scoped Real

namespace RhStatementAudit

/-! ## 0. Definitional snapshot

These hold by `rfl`: they record the *exact* unfolding of the definitions at the pinned commit.
A change upstream (or a fork) that alters the definitions makes these fail. -/

/-- The statement, unfolded. This is character-for-character the shape used in the
`Challenge.lean` of the Alpöge release (`RiemannZetaZerosOnLine`). -/
theorem riemannHypothesis_unfold :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 →
        s.re = 1 / 2 :=
  Iff.rfl

/-- `riemannZeta` is literally the even Hurwitz zeta function at `a = 0`. -/
theorem riemannZeta_unfold : riemannZeta = HurwitzZeta.hurwitzZetaEven 0 := rfl

/-- `hurwitzZetaEven a` is `Λ(s) / Γℝ(s)` with a patched value at `s = 0`. -/
theorem hurwitzZetaEven_unfold (a : UnitAddCircle) :
    HurwitzZeta.hurwitzZetaEven a =
      Function.update (fun s ↦ HurwitzZeta.completedHurwitzZetaEven a s / Gammaℝ s)
        0 (if a = 0 then -1 / 2 else 0) := rfl

/-- Mathlib's `cpow` convention (the only place a "junk" convention could leak into the series). -/
theorem cpow_convention (x y : ℂ) :
    x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y) := rfl

/-! ## 1. ζ is the Dirichlet series on `Re s > 1`

We state it with `HasSum` (not only `tsum`), since `tsum` of a non-summable family is `0` in
Mathlib: a `tsum` equation alone could be "true for junk reasons". We also use the `n + 1`
indexing, so that Mathlib's convention `0 ^ s = 0` plays no role. -/

theorem anchor_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
  have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- **Anchor 1.** On `Re s > 1`, `riemannZeta s = ∑ₙ₌₁^∞ n^{-s}` (as a genuinely convergent sum). -/
theorem anchor_hasSum_dirichlet {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact (anchor_summable hs).hasSum

/-- Same, as an equation (the Mathlib lemma `zeta_eq_tsum_one_div_nat_add_one_cpow`). -/
theorem anchor_tsum_dirichlet {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
  zeta_eq_tsum_one_div_nat_add_one_cpow hs

/-- Euler's value: a numerical sanity anchor inside the convergence region. -/
theorem anchor_zeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := riemannZeta_two

/-- A value *outside* the convergence region (genuinely tests the continuation). -/
theorem anchor_zeta_zero : riemannZeta 0 = -1 / 2 := riemannZeta_zero

/-- Another value outside the convergence region: `ζ(-1) = -1/12`. -/
theorem anchor_zeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 1
  rw [bernoulli'_two] at h
  norm_num at h
  rw [h]
  norm_num

/-! ## 2. ζ is analytic on `ℂ \ {1}`, hence uniquely determined by Anchor 1 -/

/-- **Anchor 2a.** Differentiability on `ℂ \ {1}`. -/
theorem anchor_differentiableOn : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  differentiableOn_riemannZeta

/-- **Anchor 2b.** Analyticity on `ℂ \ {1}`. -/
theorem anchor_analyticOnNhd : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  analyticOn_riemannZeta

/-- **Anchor 2c (uniqueness of the continuation).** *Any* function analytic on `ℂ \ {1}` whose
values on `Re s > 1` are given by the Dirichlet series agrees with `riemannZeta` on `ℂ \ {1}`.
Together with 1 and 2b this characterises `riemannZeta` on `ℂ \ {1}` without reference to its
definition. -/
theorem anchor_unique {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {1}ᶜ)
    (hser : ∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (f s)) :
    EqOn f riemannZeta {1}ᶜ :=
  hf.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    (eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
      fun s hs ↦ (hser s hs).unique (anchor_hasSum_dirichlet hs))

/-! ## 3. The junk value at `s = 1` and the trivial zeros -/

/-- The junk value `ζ(1) = (γ - log 4π)/2` is nonzero, so the hypothesis `s ≠ 1` in
`RiemannHypothesis` is redundant: it can neither weaken nor strengthen the statement. -/
theorem anchor_zeta_one_ne_zero : riemannZeta 1 ≠ 0 := riemannZeta_one_ne_zero

/-- The excluded points `-2(n+1)` really are zeros. -/
theorem anchor_trivial_zeros (n : ℕ) : riemannZeta (-2 * ((n : ℂ) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- Key lemma: in the closed left half-plane, the only zeros are the trivial ones (`s = 0` is not a
zero since `ζ 0 = -1/2`). Proved from the functional equation and non-vanishing on `Re ≥ 1`. -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0)
    (hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]; norm_num
  set w : ℂ := 1 - s with hw
  have hsw : s = 1 - w := by rw [hw]; ring
  have hwre : 1 ≤ w.re := by rw [hw, sub_re, one_re]; linarith
  have hw1 : w ≠ 1 := by
    intro h; apply hs0; rw [hsw, h, sub_self]
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have := congrArg re h
    simp only [neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [hsw, riemannZeta_one_sub hwn hw1]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · rw [Ne, cpow_eq_zero_iff]
    exact fun h ↦ (mul_ne_zero two_ne_zero hπ) h.1
  · exact Gamma_ne_zero_of_re_pos (by linarith)
  · intro hcos
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hwk : w = 2 * k + 1 := by
      have h2 : (π : ℂ) * w = π * (2 * k + 1) := by linear_combination 2 * hk
      exact mul_left_cancel₀ hπ h2
    have hre : w.re = 2 * k + 1 := by
      rw [hwk]; simp
    have hk0 : (0 : ℤ) ≤ k := by
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rcases m with _ | n
    · apply hs0; rw [hsw, hwk]; simp
    · apply hnt
      refine ⟨n, ?_⟩
      rw [hsw, hwk]
      push_cast
      ring
  · exact riemannZeta_ne_zero_of_one_le_re hwre

/-- **Anchor 3.** The excluded set in `RiemannHypothesis` is *exactly* the set of zeros of ζ in
`Re s ≤ 0`: nothing more is excluded (which would weaken RH) and nothing less. -/
theorem anchor_trivial_zeros_exact {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  constructor
  · intro hz
    by_contra hnt
    exact riemannZeta_ne_zero_of_re_nonpos hs hnt hz
  · rintro ⟨n, rfl⟩
    exact anchor_trivial_zeros n

/-! ## 4. Equivalent forms of `RiemannHypothesis` -/

lemma re_trivial_neg (n : ℕ) : (-2 * ((n : ℂ) + 1)).re < 0 := by
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Anchor 4a (critical-strip form).** `RiemannHypothesis` is equivalent to the textbook
"every zero of ζ in the open strip `0 < Re s < 1` lies on `Re s = 1/2`". -/
theorem riemannHypothesis_iff_strip :
    RiemannHypothesis ↔
      ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s h0 h1 hz
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩
      linarith [re_trivial_neg n]
    · rintro rfl
      simp at h1
  · intro h s hz hnt _
    rcases le_or_gt s.re 0 with h0 | h0
    · exact absurd hz (riemannZeta_ne_zero_of_re_nonpos h0 hnt)
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact h s h0 h1 hz
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h1)

/-- **Anchor 4b.** Dropping the (redundant) hypothesis `s ≠ 1`. -/
theorem riemannHypothesis_iff_no_one :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2 := by
  constructor
  · intro h s hz hnt
    exact h s hz hnt (by rintro rfl; exact riemannZeta_one_ne_zero hz)
  · intro h s hz hnt _
    exact h s hz hnt

/-- RH stated with *no reference to `riemannZeta` at all*: for every function that is analytic on
`ℂ \ {1}` and given by `∑ n^{-s}` on `Re s > 1`, its zeros in the critical strip lie on the
critical line. -/
def RiemannHypothesisViaContinuation : Prop :=
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f {1}ᶜ →
    (∀ s : ℂ, 1 < s.re → HasSum (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) (f s)) →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → f s = 0 → s.re = 1 / 2

/-- **Anchor 4c.** Mathlib's `RiemannHypothesis` is equivalent to the definition-free statement
`RiemannHypothesisViaContinuation`. Since that statement mentions only `HasSum`, `cpow` on
positive reals, and analyticity, this fixes the meaning of `RiemannHypothesis` independently of
the whole Hurwitz/Mellin/theta construction of `riemannZeta`. -/
theorem riemannHypothesis_iff_viaContinuation :
    RiemannHypothesis ↔ RiemannHypothesisViaContinuation := by
  rw [riemannHypothesis_iff_strip]
  constructor
  · intro h f hf hser s h0 h1 hz
    have hs1 : s ∈ ({1}ᶜ : Set ℂ) := by
      rintro rfl; simp at h1
    exact h s h0 h1 (by rw [← anchor_unique hf hser hs1]; exact hz)
  · intro h s h0 h1 hz
    exact h riemannZeta analyticOn_riemannZeta (fun s hs ↦ anchor_hasSum_dirichlet hs) s h0 h1 hz

end RhStatementAudit
