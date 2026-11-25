/-
`#print axioms` for every anchor. `scripts/check_axioms.py` parses the output of
`lake env lean RhStatementAudit/Axioms.lean` and fails unless every line lists only
`propext`, `Classical.choice`, `Quot.sound` (in particular: no `sorryAx`, no extra axioms).
-/
import RhStatementAudit.Eta

open RhStatementAudit

-- §0 definitional snapshot
#print axioms riemannHypothesis_unfold
#print axioms riemannZeta_unfold
#print axioms hurwitzZetaEven_unfold
#print axioms cpow_convention
-- §1 Dirichlet series
#print axioms anchor_summable
#print axioms anchor_hasSum_dirichlet
#print axioms anchor_tsum_dirichlet
#print axioms anchor_zeta_two
#print axioms anchor_zeta_zero
#print axioms anchor_zeta_neg_one
-- §2 analyticity and uniqueness of the continuation
#print axioms anchor_differentiableOn
#print axioms anchor_analyticOnNhd
#print axioms anchor_unique
-- §3 junk value and trivial zeros
#print axioms anchor_zeta_one_ne_zero
#print axioms anchor_trivial_zeros
#print axioms riemannZeta_ne_zero_of_re_nonpos
#print axioms anchor_trivial_zeros_exact
-- §4 equivalent forms of RiemannHypothesis
#print axioms riemannHypothesis_iff_strip
#print axioms riemannHypothesis_iff_no_one
#print axioms riemannHypothesis_iff_viaContinuation
-- §5 Dirichlet eta
#print axioms etaPaired_summable
#print axioms differentiableAt_etaPaired
#print axioms etaPaired_eq_of_one_lt_re
#print axioms etaPaired_eqOn_etaDomain
#print axioms etaPaired_eq_zero_iff
#print axioms riemannHypothesis_iff_viaEta
