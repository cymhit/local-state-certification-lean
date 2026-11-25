import LocalCertification.Extremal.IntegerDual
import LocalCertification.Extremal.DualMasses

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace LocalCertification.Extremal

/-- Finite atoms followed by the same certificate's infinity atom. -/
def IntegerDualCertificate.coefficient {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) :
    Fin (r+2) → ℝ := Fin.snoc c.weight c.infinityWeight

theorem IntegerDualCertificate.coefficient_mass {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : ∑ i, c.coefficient i = 1 := by
  simpa [IntegerDualCertificate.coefficient, Fin.sum_univ_castSucc] using c.mass

theorem IntegerDualCertificate.coefficient_variation {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : ∑ i, |c.coefficient i| = extremalValue q r := by
  simpa [IntegerDualCertificate.coefficient, Fin.sum_univ_castSucc] using c.variation

/-- The common normalization of the two physical mixtures. -/
def dualNormalization (q : ℝ) (r : ℕ) : ℝ := (extremalValue q r+1)/2

theorem dualNormalization_pos (q : ℝ) (hq : 1 < q) (r : ℕ) : 0 < dualNormalization q r := by
  have h := one_lt_extremalValue q hq r
  unfold dualNormalization
  linarith

theorem dualNormalization_inv (q : ℝ) (hq : 1 < q) (r : ℕ) :
    (dualNormalization q r)⁻¹ = gamma q r := by
  rw [dualNormalization, gamma_eq_extremalValue q hq r, inv_div]
  ring

theorem IntegerDualCertificate.positive_mass {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : positiveCoefficientMass c.coefficient = dualNormalization q r := by
  have h := (coefficient_mass_identities c.coefficient).1
  rw [c.coefficient_mass, c.coefficient_variation] at h
  unfold dualNormalization
  linarith

theorem IntegerDualCertificate.negative_mass {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : negativeCoefficientMass c.coefficient = dualNormalization q r-1 := by
  have h := (coefficient_mass_identities c.coefficient).2
  rw [c.coefficient_mass, c.positive_mass] at h
  linarith

/-- The actual uniform component weight is strictly positive. -/
def uniformComponentWeight {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) : ℝ :=
  |c.infinityWeight| / dualNormalization q r

theorem uniformComponentWeight_pos {q : ℝ} (hq : 1 < q) {r : ℕ}
    (c : IntegerDualCertificate q r) : 0 < uniformComponentWeight c :=
  div_pos (abs_pos.mpr c.infinityWeight_ne_zero) (dualNormalization_pos q hq r)

end LocalCertification.Extremal
