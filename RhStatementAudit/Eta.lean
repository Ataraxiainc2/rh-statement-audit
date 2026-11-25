/-
Copyright (c) 2026. Released under Apache 2.0 license.

# RH via an explicit Dirichlet eta series, independent of `riemannZeta`

**Design note (why the series is paired).** The textbook alternating series
`η(s) = ∑ₙ (-1)ⁿ⁻¹ n⁻ˢ` converges only *conditionally* for `0 < Re s ≤ 1`. Mathlib's `tsum`
requires *unconditional* summability and returns the junk value `0` otherwise; so
`∑' n, (-1)^n / (n+1)^s` would be `0` on the whole critical strip, and "RH via that `tsum`" would
be a false statement about a junk value. We therefore use the paired series

  `η(s) = ∑ₖ ((2k+1)⁻ˢ - (2k+2)⁻ˢ)`

whose terms are `O(|s| (2k+1)^{-Re s - 1})`, so it converges *absolutely* on `Re s > 0`
(proved below: `etaPaired_summable`). It is the same function as the alternating series wherever
the latter converges.

Main result: `riemannHypothesis_iff_viaEta : RiemannHypothesis ↔ RiemannHypothesisViaEta`,
where `RiemannHypothesisViaEta` does not mention `riemannZeta`.
-/
import RhStatementAudit.Anchors

open Complex Filter Topology Set
open scoped Real

namespace RhStatementAudit

/-- The `k`-th paired term `(2k+1)⁻ˢ - (2k+2)⁻ˢ`. -/
noncomputable def etaTerm (k : ℕ) (s : ℂ) : ℂ :=
  1 / (2 * (k : ℂ) + 1) ^ s - 1 / (2 * (k : ℂ) + 2) ^ s

/-- Dirichlet's eta function as an explicit (absolutely convergent on `Re s > 0`) series. -/
noncomputable def etaPaired (s : ℂ) : ℂ := ∑' k : ℕ, etaTerm k s

/-- RH formulated with the explicit eta series; `riemannZeta` does not occur. -/
def RiemannHypothesisViaEta : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → etaPaired s = 0 → s.re = 1 / 2

/-! ### Analytic estimates -/

/-- Mean value bound: `‖a⁻ʷ - (a+1)⁻ʷ‖ ≤ ‖w‖ a^{-Re w - 1}` for `a > 0`, `Re w ≥ 0`. -/
lemma norm_cpow_neg_sub_le {a : ℝ} (ha : 0 < a) (w : ℂ) (hw : 0 ≤ w.re) :
    ‖(a : ℂ) ^ (-w) - ((a + 1 : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-w)
  let f' : ℝ → ℂ := fun t ↦ -w * (t : ℂ) ^ (-w - 1)
  have hderiv : ∀ t ∈ Icc a (a + 1), HasDerivWithinAt f (f' t) (Icc a (a + 1)) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((Complex.hasStrictDerivAt_cpow_const (c := -w)
      (ofReal_mem_slitPlane.mpr ht0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico a (a + 1), ‖f' t‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simp only [f', norm_mul, norm_neg]
    rw [norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith))
      (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
    ⟨by linarith, le_rfl⟩
  rw [norm_sub_rev]
  simpa [f] using h

lemma two_mul_add_one_ne_zero (k : ℕ) : (2 * (k : ℂ) + 1) ≠ 0 := by
  have : (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this]; exact Nat.cast_ne_zero.mpr (by omega)

lemma two_mul_add_two_ne_zero (k : ℕ) : (2 * (k : ℂ) + 2) ≠ 0 := by
  have : (2 * (k : ℂ) + 2) = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [this]; exact Nat.cast_ne_zero.mpr (by omega)

lemma etaTerm_eq_rpow (k : ℕ) (s : ℂ) :
    etaTerm k s =
      (((2 * k + 1 : ℝ)) : ℂ) ^ (-s) - ((((2 * k + 1 : ℝ)) + 1 : ℝ) : ℂ) ^ (-s) := by
  have e1 : (((2 * k + 1 : ℝ)) : ℂ) = 2 * (k : ℂ) + 1 := by push_cast; ring
  have e2 : ((((2 * k + 1 : ℝ)) + 1 : ℝ) : ℂ) = 2 * (k : ℂ) + 2 := by push_cast; ring
  rw [e1, e2, etaTerm, cpow_neg, cpow_neg, one_div, one_div]

lemma norm_etaTerm_le (k : ℕ) (w : ℂ) (hw : 0 ≤ w.re) :
    ‖etaTerm k w‖ ≤ ‖w‖ * ((2 * k + 1 : ℝ)) ^ (-w.re - 1) := by
  rw [etaTerm_eq_rpow]
  exact norm_cpow_neg_sub_le (by positivity) w hw

lemma summable_odd_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun k : ℕ ↦ ((2 * k + 1 : ℝ)) ^ p) := by
  have h1 : Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ p) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine h1.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

/-- **Anchor (eta is a genuine sum).** For `Re s > 0` the paired eta series is absolutely
summable, so `etaPaired s` is never a junk `tsum` value in the region we use it. -/
theorem etaPaired_summable {s : ℂ} (hs : 0 < s.re) : Summable (fun k ↦ etaTerm k s) := by
  refine Summable.of_norm_bounded ((summable_odd_rpow (p := -s.re - 1) (by linarith)).mul_left ‖s‖)
    (fun k ↦ norm_etaTerm_le k s hs.le)

lemma differentiableAt_etaTerm (k : ℕ) (w : ℂ) : DifferentiableAt ℂ (etaTerm k) w := by
  have hc1 := two_mul_add_one_ne_zero k
  have hc2 := two_mul_add_two_ne_zero k
  have hp1 : DifferentiableAt ℂ (fun w : ℂ ↦ (2 * (k : ℂ) + 1) ^ w) w :=
    DifferentiableAt.const_cpow differentiableAt_fun_id (Or.inl hc1)
  have hp2 : DifferentiableAt ℂ (fun w : ℂ ↦ (2 * (k : ℂ) + 2) ^ w) w :=
    DifferentiableAt.const_cpow differentiableAt_fun_id (Or.inl hc2)
  have hn1 : (2 * (k : ℂ) + 1) ^ w ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hc1 h.1
  have hn2 : (2 * (k : ℂ) + 2) ^ w ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hc2 h.1
  exact ((differentiableAt_const _).div hp1 hn1).sub ((differentiableAt_const _).div hp2 hn2)

/-- The eta series is holomorphic on `Re s > 0`. -/
theorem differentiableAt_etaPaired {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ etaPaired s₀ := by
  set σ : ℝ := s₀.re / 2 with hσ
  set R : ℝ := ‖s₀‖ + 1 with hR
  let V : Set ℂ := {w | σ < w.re} ∩ {w | ‖w‖ < R}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hs₀V : s₀ ∈ V := ⟨by show σ < s₀.re; linarith, by show ‖s₀‖ < R; linarith⟩
  have hσ0 : 0 < σ := by linarith
  have hdiff : DifferentiableOn ℂ (fun w ↦ ∑' k : ℕ, etaTerm k w) V := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k : ℕ ↦ R * ((2 * k + 1 : ℝ)) ^ (-σ - 1))
      ((summable_odd_rpow (by linarith)).mul_left R)
      (fun k ↦ fun w _ ↦ (differentiableAt_etaTerm k w).differentiableWithinAt) hV ?_
    intro k w hw
    have hw1 : σ < w.re := hw.1
    have hw2 : ‖w‖ < R := hw.2
    have hk : (1 : ℝ) ≤ 2 * k + 1 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    calc ‖etaTerm k w‖ ≤ ‖w‖ * ((2 * k + 1 : ℝ)) ^ (-w.re - 1) :=
          norm_etaTerm_le k w (by linarith)
      _ ≤ R * ((2 * k + 1 : ℝ)) ^ (-σ - 1) := by
          apply mul_le_mul hw2.le (Real.rpow_le_rpow_of_exponent_le hk (by linarith))
            (by positivity) (by positivity)
  exact hdiff.differentiableAt (hV.mem_nhds hs₀V)

/-! ### Relation with ζ on `Re s > 1` -/

lemma two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]

/-- For `Re s > 1`: `η(s) = (1 - 2^{1-s}) ζ(s)`. -/
theorem etaPaired_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaPaired s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1) ^ s with hfdef
  have hf : Summable f := anchor_summable hs
  have he : Summable (fun k : ℕ ↦ f (2 * k)) :=
    hf.comp_injective (i := fun k : ℕ ↦ 2 * k) (fun a b h ↦ by simp only at h; omega)
  have ho : Summable (fun k : ℕ ↦ f (2 * k + 1)) :=
    hf.comp_injective (i := fun k : ℕ ↦ 2 * k + 1) (fun a b h ↦ by simp only at h; omega)
  have hsplit : ∑' k, f (2 * k) + ∑' k, f (2 * k + 1) = ∑' k, f k := tsum_even_add_odd he ho
  have hζ : ∑' k, f k = riemannZeta s := (anchor_tsum_dirichlet hs).symm
  have hodd : ∀ k : ℕ, f (2 * k + 1) = 2 ^ (-s) * f k := by
    intro k
    simp only [hfdef]
    have e : (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, mul_cpow_ofReal_nonneg (by norm_num) (by positivity), cpow_neg]
    push_cast
    field_simp
  have hO : ∑' k, f (2 * k + 1) = 2 ^ (-s) * riemannZeta s := by
    rw [tsum_congr hodd, tsum_mul_left, hζ]
  have hterm : ∀ k : ℕ, etaTerm k s = f (2 * k) - f (2 * k + 1) := by
    intro k
    simp only [etaTerm, hfdef]
    push_cast
    ring_nf
  have hE : ∑' k, f (2 * k) = riemannZeta s - 2 ^ (-s) * riemannZeta s := by
    rw [← hO, ← hζ, ← hsplit]; ring
  rw [etaPaired, tsum_congr hterm, he.tsum_sub ho, hE, hO, two_cpow_one_sub]
  ring

/-! ### A preconnected open domain containing the critical strip and avoiding `s = 1` -/

/-- `{Re>0, Im>0} ∪ {Re>1} ∪ {Re>0, Im<0} ∪ B(1/2, 1/2)`. -/
def etaDomain : Set ℂ :=
  (({w : ℂ | 0 < w.re} ∩ {w | 0 < w.im}) ∪ {w | 1 < w.re}) ∪
    ({w : ℂ | 0 < w.re} ∩ {w | w.im < 0}) ∪ Metric.ball (1 / 2 : ℂ) (1 / 2)

lemma isOpen_etaDomain : IsOpen etaDomain := by
  unfold etaDomain
  refine (((IsOpen.inter ?_ ?_).union ?_).union (IsOpen.inter ?_ ?_)).union Metric.isOpen_ball
  · exact isOpen_lt continuous_const continuous_re
  · exact isOpen_lt continuous_const continuous_im
  · exact isOpen_lt continuous_const continuous_re
  · exact isOpen_lt continuous_const continuous_re
  · exact isOpen_lt continuous_im continuous_const

lemma mem_ball_half_iff (w : ℂ) : w ∈ Metric.ball (1 / 2 : ℂ) (1 / 2) ↔ ‖w - 1 / 2‖ < 1 / 2 := by
  rw [Metric.mem_ball, dist_eq_norm]

lemma etaDomain_sub {w : ℂ} (hw : w ∈ etaDomain) : 0 < w.re ∧ w ≠ 1 := by
  rcases hw with ((⟨h1, h2⟩ | h) | ⟨h1, h2⟩) | h
  · refine ⟨h1, ?_⟩; rintro rfl; simp at h2
  · have h' : 1 < w.re := h
    refine ⟨by linarith, ?_⟩; rintro rfl; simp at h'
  · refine ⟨h1, ?_⟩; rintro rfl; simp at h2
  · rw [mem_ball_half_iff] at h
    have hre := abs_re_le_norm (w - 1 / 2)
    have : (w - 1 / 2).re = w.re - 1 / 2 := by simp
    rw [this] at hre
    refine ⟨by linarith [neg_abs_le (w.re - 1 / 2)], ?_⟩
    rintro rfl
    norm_num at h

lemma strip_sub_etaDomain {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : s ∈ etaDomain := by
  rcases lt_trichotomy s.im 0 with h | h | h
  · exact Or.inl (Or.inr ⟨h0, h⟩)
  · refine Or.inr ?_
    rw [mem_ball_half_iff]
    have him : (s - 1 / 2).im = 0 := by simp [h]
    rw [← (abs_re_eq_norm.mpr him)]
    have : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [this, abs_sub_lt_iff]
    constructor <;> linarith
  · exact Or.inl (Or.inl (Or.inl ⟨h0, h⟩))

lemma two_mem_etaDomain : (2 : ℂ) ∈ etaDomain :=
  Or.inl (Or.inl (Or.inr (by show (1 : ℝ) < (2 : ℂ).re; norm_num)))

lemma isPreconnected_etaDomain : IsPreconnected etaDomain := by
  have hA : IsPreconnected ({w : ℂ | 0 < w.re} ∩ {w | 0 < w.im}) :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected {w : ℂ | 1 < w.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hC : IsPreconnected ({w : ℂ | 0 < w.re} ∩ {w | w.im < 0}) :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected (Metric.ball (1 / 2 : ℂ) (1 / 2)) := (convex_ball _ _).isPreconnected
  have hAB := IsPreconnected.union (2 + I) (by constructor <;> simp) (by norm_num) hA hB
  have hABC := IsPreconnected.union (2 - I) (Or.inr (by norm_num))
    (by constructor <;> simp) hAB hC
  refine IsPreconnected.union (1 / 2 + I / 4) (Or.inl (Or.inl ⟨by simp, by simp⟩)) ?_ hABC hD
  rw [mem_ball_half_iff]
  have : (1 / 2 + I / 4 - 1 / 2 : ℂ) = I / 4 := by ring
  rw [this, norm_div, norm_I]
  norm_num

/-! ### Identity principle and the equivalence -/

theorem etaPaired_eqOn_etaDomain :
    EqOn etaPaired (fun s ↦ (1 - 2 ^ (1 - s)) * riemannZeta s) etaDomain := by
  have h1 : AnalyticOnNhd ℂ etaPaired etaDomain :=
    DifferentiableOn.analyticOnNhd
      (fun w hw ↦ (differentiableAt_etaPaired (etaDomain_sub hw).1).differentiableWithinAt)
      isOpen_etaDomain
  have h2 : AnalyticOnNhd ℂ (fun s ↦ (1 - 2 ^ (1 - s)) * riemannZeta s) etaDomain := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) isOpen_etaDomain
    have hc : DifferentiableAt ℂ (fun s : ℂ ↦ (2 : ℂ) ^ (1 - s)) w :=
      DifferentiableAt.const_cpow ((differentiableAt_const _).sub differentiableAt_fun_id)
        (Or.inl two_ne_zero)
    exact (((differentiableAt_const _).sub hc).mul
      (differentiableAt_riemannZeta (etaDomain_sub hw).2)).differentiableWithinAt
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_etaDomain two_mem_etaDomain
    (eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
      fun s hs ↦ etaPaired_eq_of_one_lt_re hs)

lemma one_sub_two_cpow_ne_zero {s : ℂ} (h1 : s.re < 1) : (1 : ℂ) - 2 ^ (1 - s) ≠ 0 := by
  intro h
  have h' : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -h
  have hn := congrArg norm h'
  have e : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [e, norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hn
  have : (1 : ℝ) < (2 : ℝ) ^ (1 - s).re :=
    Real.one_lt_rpow (by norm_num) (by simp; linarith)
  linarith

/-- In the critical strip, zeros of the explicit eta series are exactly the zeros of ζ. -/
theorem etaPaired_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    etaPaired s = 0 ↔ riemannZeta s = 0 := by
  have := etaPaired_eqOn_etaDomain (strip_sub_etaDomain h0 h1)
  simp only at this
  rw [this, mul_eq_zero, or_iff_right (one_sub_two_cpow_ne_zero h1)]

/-- **Anchor 4d.** Mathlib's `RiemannHypothesis` is equivalent to RH for the explicit eta series,
a statement in which `riemannZeta` does not occur. -/
theorem riemannHypothesis_iff_viaEta : RiemannHypothesis ↔ RiemannHypothesisViaEta := by
  rw [riemannHypothesis_iff_strip]
  constructor
  · intro h s h0 h1 hz
    exact h s h0 h1 ((etaPaired_eq_zero_iff h0 h1).mp hz)
  · intro h s h0 h1 hz
    exact h s h0 h1 ((etaPaired_eq_zero_iff h0 h1).mpr hz)

end RhStatementAudit
