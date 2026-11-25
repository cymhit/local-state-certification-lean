import CertificationGaussian.FiniteComplementRemainder
import Mathlib.Data.Fintype.Powerset

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- All subsets of order j, with j running from zero through r, as actual finite labelled choices. -/
abbrev CardinalityComplementIndex (S : Type*) (r : ℕ) :=
  (j : Fin (r+1)) × {A : Finset S // A.card=j.val}

def cardinalityComplementSet {S : Type*} {r : ℕ} (k : CardinalityComplementIndex S r) : Finset S := k.2.val

def cardinalityComplementWeight {S : Type*} {r : ℕ} (lam : ℕ → ℝ)
    (k : CardinalityComplementIndex S r) : ℝ := lam k.1.val

theorem cardinalityComplementSet_order {S : Type*} {r : ℕ} (k : CardinalityComplementIndex S r) :
    (cardinalityComplementSet k).card≤r := by
  change k.2.val.card≤r
  rw [k.2.property]
  exact Nat.le_of_lt_succ k.1.isLt

/-- The absolute weighted shell mass, with the multiplicity factor (d−1)ʲ. -/
def complementLambda (d n r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (r+1),|lam j.val| *(n.choose j.val:ℝ)*((d:ℝ)-1)^j.val

section FiniteSites
variable {S Ω : Type*} [Fintype S] [DecidableEq S]

/-- The actual cardinality-based kernel H_s of the paper, using the same local recorded P and I-P. -/
def cardinalityReadoutKernel (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (r : ℕ) (lam : ℕ → ℝ) (ω : S → Ω) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  finiteComplementKernel d record (cardinalityComplementSet (S:=S) (r:=r))
    (cardinalityComplementWeight lam) ω

/-- The actual kernel is precisely sum_{j=0}^r lambda_j sum_{|J|=j} Q_s(J). -/
theorem cardinalityReadoutKernel_formula (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (r : ℕ) (lam : ℕ → ℝ) (ω : S → Ω) :
    cardinalityReadoutKernel d record r lam ω =
      ∑ j : Fin (r+1),(lam j.val:ℂ) •
        ∑ J : {A : Finset S // A.card=j.val},productReadoutFactor d record J.val ω := by
  simp only [cardinalityReadoutKernel,finiteComplementKernel,Fintype.sum_sigma,
    cardinalityComplementSet,cardinalityComplementWeight,Finset.smul_sum]

omit [DecidableEq S] in
/-- Subsets with j sites have the real binomial multiplicity, including j>n where the fiber is empty. -/
theorem cardinalityComplement_coefficient_mass (r : ℕ) (lam : ℕ → ℝ) :
    (∑ k : CardinalityComplementIndex S r,|cardinalityComplementWeight lam k|) =
      ∑ j : Fin (r+1),|lam j.val| *((Fintype.card S).choose j.val:ℝ) := by
  simp only [cardinalityComplementWeight,Fintype.sum_sigma,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Fintype.card_finset_len]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq S] in
/-- The paper's Lambda_n dominates the exact coefficient mass for every physical local dimension. -/
theorem cardinalityComplement_mass_le_Lambda (d : ℕ) (hd : 2≤d) (r : ℕ) (lam : ℕ → ℝ) :
    (∑ k : CardinalityComplementIndex S r,|cardinalityComplementWeight lam k|) ≤
      complementLambda d (Fintype.card S) r lam := by
  rw [cardinalityComplement_coefficient_mass]
  apply Finset.sum_le_sum
  intro j _
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    (one_le_pow₀ (by linarith))

/-- The actual Z_z built from the cardinality kernel and the full product reference-record measure. -/
def cardinalityReadoutRemainder [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  finiteComplementRemainder d μ record (cardinalityComplementSet (S:=S) (r:=r))
    (cardinalityComplementWeight lam) z

/-- This is exactly D times the actual matrix integral of P_s W_z(H_s,H_s). -/
theorem cardinalityReadoutRemainder_formula [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) :
    cardinalityReadoutRemainder d μ record r lam z = (d:ℝ)^(Fintype.card S) •
      ∫ ω,complexGaussianNormalMatrix (cardinalityReadoutKernel d record r lam ω)
        (cardinalityReadoutKernel d record r lam ω) z • productRecordedProjector d record ω
          ∂Measure.pi (fun _ : S => μ) := rfl

/-- The paper's actual cardinality kernel remainder is Hermitian for all real coefficients, without sign restrictions. -/
theorem cardinalityReadoutRemainder_isHermitian [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (r : ℕ) (lam : ℕ → ℝ) (z : (S → Fin d) → ℂ) :
    (cardinalityReadoutRemainder d μ record r lam z).IsHermitian :=
  finiteComplementRemainder_isHermitian d μ record hr _ _ z

/-- The true full-Haar finite-complement remainder bound with the original Lambda_n. -/
theorem cardinalityHaar_remainder_bound (d : ℕ) [NeZero d] (hd : 3≤d) (r : ℕ) (lam : ℕ → ℝ) :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=S) d (haarBasisRecords d) id r lam
      (complexCoordinate z))^4)).re ∂pairedGaussian (S → Fin d)) ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d (Fintype.card S) r lam)^8*(haarLocalKappa d)^(Fintype.card S-8*r) := by
  have h := finiteComplementHaar_remainder_bound d hd r (cardinalityComplementSet (S:=S) (r:=r))
    cardinalityComplementSet_order (cardinalityComplementWeight lam)
  apply h.trans
  have hm := cardinalityComplement_mass_le_Lambda (S:=S) d (by omega) r lam
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hm 8
  have hκ := haarLocalKappa_pos d (by omega)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

/-- The true three-Pauli-basis remainder bound with exactly Lambda_n and C2=16. -/
theorem cardinalityPauli_remainder_bound (r : ℕ) (lam : ℕ → ℝ) :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=S) 2 pauliBasisRecords pauliFullRecord r lam
      (complexCoordinate z))^4)).re ∂pairedGaussian (S → Fin 2)) ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(complementLambda 2 (Fintype.card S) r lam)^8*
        pauliLocalKappa^(Fintype.card S-8*r) := by
  have h := finiteComplementPauli_remainder_bound r (cardinalityComplementSet (S:=S) (r:=r))
    cardinalityComplementSet_order (cardinalityComplementWeight lam)
  apply h.trans
  have hm := cardinalityComplement_mass_le_Lambda (S:=S) 2 (by decide) r lam
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hm 8
  have hκ := pauliLocalKappa_pos
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)

end FiniteSites
end CertificationGaussian
