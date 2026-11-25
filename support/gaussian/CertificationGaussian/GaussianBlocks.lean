import CertificationGaussian.IndependentQuadratic

noncomputable section
open MeasureTheory ProbabilityTheory
namespace CertificationGaussian
variable (I : Type*) [Fintype I]

/-- Keep the real/imaginary labels while splitting the coordinate index into two copies. -/
def pairSumIndex : (Fin 2 × I) ≃ I ⊕ I where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i => (0,i)) (fun i => (1,i))
  left_inv := by rintro ⟨s,i⟩; fin_cases s <;> rfl
  right_inv := by intro i; cases i <;> rfl

/-- Regroup the same real Gaussian coordinates into pairs; no new random model is assumed. -/
def blockCoordinates : ((Fin 2 × I) → ℝ) ≃ᵐ (I → ℝ × ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : I ⊕ I => ℝ) (pairSumIndex I)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ I => ℝ))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).symm

omit [Fintype I] in
theorem blockCoordinates_apply (x : (Fin 2 × I) → ℝ) (i : I) :
    blockCoordinates I x i = (x (0,i), x (1,i)) := rfl

theorem blockCoordinates_preserving : MeasurePreserving (blockCoordinates I)
    (pairedGaussian I) (blockGaussian I) := by
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm.comp
    ((measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ I => gaussianReal 0 1)).comp
      (measurePreserving_piCongrLeft (fun _ : I ⊕ I => gaussianReal 0 1) (pairSumIndex I)))

variable {I}
omit [Fintype I] in
theorem complexCoordinate_normSq (x : (Fin 2 × I) → ℝ) (i : I) :
    Complex.normSq (complexCoordinate x i) = radialPairOutcome (blockCoordinates I x i) + 1 := by
  simp only [complexCoordinate, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
    blockCoordinates_apply, radialPairOutcome]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [← pow_two, ← pow_two, div_pow, div_pow, hs]
  ring

theorem gaussianOutcome_identity [DecidableEq I] (x : (Fin 2 × I) → ℝ) (i : I) :
    gaussianOutcome (1 : Matrix I I ℂ) x i = radialPairOutcome (blockCoordinates I x i) := by
  simp only [gaussianOutcome, Matrix.one_mulVec, complexCoordinate_normSq, add_sub_cancel_right]

end CertificationGaussian
