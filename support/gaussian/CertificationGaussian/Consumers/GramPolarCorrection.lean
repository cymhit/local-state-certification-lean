import CertificationGaussian.GramPolarCorrection

noncomputable section
open Matrix MeasureTheory Metric Set CFC
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian.Consumers

/-- The same genuine orbit matrix from the probability theorem admits the canonical correction on its good event. -/
theorem unitaryOrbit_polar_on_good_event {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (t : ℝ) (ht : t<1)
    (hgood : ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖ ≤ t) :
    let V := unitaryOrbitMatrix W ψ
    let Q := matrixPolarCorrection V
    Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖ ≤ t ∧
      (∀ x : EuclideanSpace ℂ K, ‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
      (∀ A : Matrix K K ℂ, ‖V*A*Vᴴ-Q*A*Qᴴ‖ ≤ 3*‖A‖*t) := by
  dsimp only
  have hg : ‖(unitaryOrbitMatrix W ψ)ᴴ*unitaryOrbitMatrix W ψ-1‖ ≤ t := hgood
  have h := matrixPolarCorrection_threshold (unitaryOrbitMatrix W ψ) ht hg
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro x
    exact rectangularEuclideanCLM_norm_map_of_gram _ h.1 x
  · intro A
    exact matrixPolarCorrection_conjugation_le _ A ht hg

/-- Probability and deterministic correction use one and the same measurable Gram event. -/
theorem unitaryOrbit_haar_polar_good_event {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0)
    (t : ℝ) (ht0 : 0<t) (ht1 : t<1) (ψ₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    complexUnitaryHaar I
      {U | t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ)
        (unitaryOrbitGramError W (complexUnitarySphereAction I U ψ₀))‖} ≤
      ENNReal.ofReal ((Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/(((Fintype.card I:ℝ)+1)*t^2)) ∧
    ∀ U, ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ)
      (unitaryOrbitGramError W (complexUnitarySphereAction I U ψ₀))‖ ≤ t →
      let V := unitaryOrbitMatrix W (complexUnitarySphereAction I U ψ₀)
      (matrixPolarCorrection V)ᴴ*matrixPolarCorrection V = 1 ∧
        ‖rectangularEuclideanCLM (V-matrixPolarCorrection V)‖ ≤ t := by
  refine ⟨unitaryOrbitGram_haar_tail W hW hHS t ht0 ψ₀, ?_⟩
  intro U hg
  have h := unitaryOrbit_polar_on_good_event W (complexUnitarySphereAction I U ψ₀) t ht1 hg
  exact ⟨h.1,h.2.1⟩

/-- A genuinely nonisometric rectangular input with Gram 5/4, safely inside the good event. -/
def tallPolarInput : Matrix (Fin 2) (Fin 1) ℂ := !![1;1/2]

theorem tallPolarInput_gram : tallPolarInputᴴ*tallPolarInput = (5/4:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [tallPolarInput, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat]

theorem tallPolarInput_error : ‖tallPolarInputᴴ*tallPolarInput-1‖ = (1:ℝ)/4 := by
  rw [tallPolarInput_gram]
  have he : (5/4:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)-1 = (1/4:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num
  rw [he, norm_smul, norm_one, mul_one]
  norm_num

theorem tallPolarInput_actual_correction :
    (matrixPolarCorrection tallPolarInput)ᴴ*matrixPolarCorrection tallPolarInput = 1 ∧
      ‖tallPolarInput-matrixPolarCorrection tallPolarInput‖ ≤ (1:ℝ)/4 ∧
      (∀ x : EuclideanSpace ℂ (Fin 1),
        ‖rectangularEuclideanCLM (matrixPolarCorrection tallPolarInput) x‖=‖x‖) := by
  have h := matrixPolarCorrection_threshold tallPolarInput (by norm_num : (1:ℝ)/4<1) tallPolarInput_error.le
  exact ⟨h.1,h.2.1,rectangularEuclideanCLM_norm_map_of_gram _ h.1⟩

/-- Already-isometric matrices are fixed by the actual CFC correction. -/
theorem isometric_polar_fixed {R C : Type*} [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] (V : Matrix R C ℂ) (hV : Vᴴ*V=1) :
    matrixPolarCorrection V=V := by
  simp [matrixPolarCorrection, matrixGramInverseSqrt, hV]

/-- Empty-column and empty-row matrices remain genuine zero-dimensional cases. -/
theorem empty_polar_dimensions (r c : ℕ) (V : Matrix (Fin r) (Fin 0) ℂ)
    (W : Matrix (Fin 0) (Fin c) ℂ) : matrixPolarCorrection V=V ∧ matrixPolarCorrection W=W :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end CertificationGaussian.Consumers
