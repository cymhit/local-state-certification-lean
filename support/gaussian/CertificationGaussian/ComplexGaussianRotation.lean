import CertificationGaussian.ComplexGaussianChaos
import CertificationGaussian.GaussianRotation

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable (I : Type*) [Fintype I] [DecidableEq I]

/-- Copy labels are sums; the inner Fin 2 label remains the real/imaginary coordinate label. -/
def gaussianCopyCoordinates : ((Fin 2 × (I ⊕ I)) → ℝ) ≃ᵐ
    (((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : (Fin 2 × I) ⊕ (Fin 2 × I) => ℝ)
    (Equiv.prodSumDistrib (Fin 2) I I)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin 2 × I) ⊕ (Fin 2 × I) => ℝ))

omit [DecidableEq I] in
theorem gaussianCopyCoordinates_preserving : MeasurePreserving (gaussianCopyCoordinates I)
    (pairedGaussian (I ⊕ I)) ((pairedGaussian I).prod (pairedGaussian I)) :=
  (measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin 2 × I) ⊕ (Fin 2 × I) => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft
      (fun _ : (Fin 2 × I) ⊕ (Fin 2 × I) => gaussianReal 0 1)
      (Equiv.prodSumDistrib (Fin 2) I I))

def gaussianHadamardMatrix : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  ((Real.sqrt 2:ℂ)⁻¹) • Matrix.fromBlocks 1 1 1 (-1)

theorem gaussianHadamardMatrix_unitary : gaussianHadamardMatrix I ∈ unitary (Matrix (I ⊕ I) (I ⊕ I) ℂ) := by
  let B : Matrix (I ⊕ I) (I ⊕ I) ℂ := Matrix.fromBlocks 1 1 1 (-1)
  have hBstar : Bᴴ = B := by simp [B, Matrix.fromBlocks_conjTranspose]
  have hBsq : B*B = (2:ℂ) • (1 : Matrix (I ⊕ I) (I ⊕ I) ℂ) := by
    ext (a | a) (b | b) <;> by_cases h : a=b <;>
      simp [B, Matrix.fromBlocks_multiply, h] <;> norm_num
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  rw [Matrix.mem_unitaryGroup_iff']
  change (((Real.sqrt 2:ℂ)⁻¹) • B)ᴴ * (((Real.sqrt 2:ℂ)⁻¹) • B) = 1
  rw [Matrix.conjTranspose_smul, hBstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBsq, smul_smul]
  have hc : star ((Real.sqrt 2:ℂ)⁻¹) * (Real.sqrt 2:ℂ)⁻¹ * 2 = 1 := by
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp [hs0]
    exact hs.symm
  rw [hc, one_smul]

/-- The actual complex 45-degree transformation on two copies. -/
def complexPairRotation (z : (I → ℂ) × (I → ℂ)) : (I → ℂ) × (I → ℂ) :=
  ((fun i => (z.1 i+z.2 i)/(Real.sqrt 2:ℂ)),
    (fun i => (z.1 i-z.2 i)/(Real.sqrt 2:ℂ)))

def complexSumSplit (z : I ⊕ I → ℂ) : (I → ℂ) × (I → ℂ) :=
  (fun i => z (Sum.inl i), fun i => z (Sum.inr i))

theorem gaussianHadamardMatrix_split (z : I ⊕ I → ℂ) :
    complexSumSplit I ((gaussianHadamardMatrix I).mulVec z) =
      complexPairRotation I (complexSumSplit I z) := by
  ext i <;> simp [complexSumSplit, complexPairRotation, gaussianHadamardMatrix,
    Matrix.smul_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec,
    div_eq_mul_inv, mul_comm, sub_eq_add_neg]

omit [Fintype I] [DecidableEq I] in
theorem gaussianCopyCoordinates_complex (x : Fin 2 × (I ⊕ I) → ℝ) :
    complexSumSplit I (complexCoordinate x) =
      (complexCoordinate (gaussianCopyCoordinates I x).1,
        complexCoordinate (gaussianCopyCoordinates I x).2) := rfl

/-- The two actual normalized complex coordinate vectors. -/
def complexPairCoordinates (x : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ)) :
    (I → ℂ) × (I → ℂ) := (complexCoordinate x.1, complexCoordinate x.2)

omit [Fintype I] [DecidableEq I] in
@[fun_prop] theorem complexPairCoordinates_continuous : Continuous (complexPairCoordinates I) := by
  unfold complexPairCoordinates complexCoordinate
  fun_prop

omit [Fintype I] [DecidableEq I] in
@[fun_prop] theorem complexPairRotation_continuous : Continuous (complexPairRotation I) := by
  unfold complexPairRotation
  fun_prop

omit [Fintype I] [DecidableEq I] in
@[fun_prop] theorem complexSumSplit_continuous : Continuous (complexSumSplit I) := by
  unfold complexSumSplit
  fun_prop

omit [DecidableEq I] in
/-- The joint complex law is identified with the existing single Gaussian on the sum index. -/
theorem complexPairCoordinates_map :
    (pairedGaussian (I ⊕ I)).map (fun x => complexSumSplit I (complexCoordinate x)) =
      ((pairedGaussian I).prod (pairedGaussian I)).map (complexPairCoordinates I) := by
  rw [← (gaussianCopyCoordinates_preserving I).map_eq,
    Measure.map_map (complexPairCoordinates_continuous I).measurable
      (gaussianCopyCoordinates I).measurable]
  rfl

/-- The genuine 45-degree rotation preserves the joint standard complex Gaussian law. -/
theorem complexPairRotation_map :
    ((pairedGaussian I).prod (pairedGaussian I)).map
      (fun z => complexPairRotation I (complexPairCoordinates I z)) =
      ((pairedGaussian I).prod (pairedGaussian I)).map (complexPairCoordinates I) := by
  have hmcoord : Measurable (complexCoordinate (I := I ⊕ I)) := by
    unfold complexCoordinate
    fun_prop
  have hmU : Measurable (fun x : (Fin 2 × (I ⊕ I)) → ℝ =>
      (gaussianHadamardMatrix I).mulVec (complexCoordinate x)) := by
    unfold complexCoordinate
    fun_prop
  have h := congrArg (fun ν : Measure (I ⊕ I → ℂ) => ν.map (complexSumSplit I))
    (complexCoordinate_unitary_map (gaussianHadamardMatrix I) (gaussianHadamardMatrix_unitary I))
  rw [Measure.map_map (complexSumSplit_continuous I).measurable hmU,
    Measure.map_map (complexSumSplit_continuous I).measurable hmcoord] at h
  simp only [Function.comp_def, gaussianHadamardMatrix_split] at h
  have hmrot : Measurable (fun z => complexPairRotation I (complexPairCoordinates I z)) :=
    ((complexPairRotation_continuous I).comp (complexPairCoordinates_continuous I)).measurable
  rw [← (gaussianCopyCoordinates_preserving I).map_eq,
    Measure.map_map hmrot (gaussianCopyCoordinates I).measurable,
    Measure.map_map (complexPairCoordinates_continuous I).measurable
      (gaussianCopyCoordinates I).measurable]
  exact h

end CertificationGaussian
