import CertificationGaussian.UnitaryOrbitGram
import CertificationGaussian.Consumers.UnitaryGaussianChaos

noncomputable section
open Matrix MeasureTheory Metric Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The actual finite-family Haar event, for every positive dimension and any fixed starting unit vector. -/
theorem finite_unitary_orbit_haar_probability (D m : ℕ) (hD : 0<D)
    (W : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix (Fin D) (Fin D) ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (D:ℂ) else 0)
    (t : ℝ) (ht : 0<t) (ψ₀ : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    complexUnitaryHaar (Fin D)
      {U | t < ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ)
        (unitaryOrbitGramError W (complexUnitarySphereAction (Fin D) U ψ₀))‖} ≤
      ENNReal.ofReal ((m:ℝ)*((m:ℝ)-1)/(((D:ℝ)+1)*t^2)) := by
  let : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  simpa only [Fintype.card_fin] using unitaryOrbitGram_haar_tail W hW (by simpa using hHS) t ht ψ₀

/-- An empty family has an actual zero Gram-error matrix, with no positive-D premise needed. -/
theorem empty_orbit_gram (D : ℕ) (W : Fin 0 → Matrix (Fin D) (Fin D) ℂ)
    (ψ : EuclideanSpace ℂ (Fin D)) : unitaryOrbitGramError W ψ = 0 ∧ unitaryOrbitGramSquareSum W ψ = 0 := by
  refine ⟨Subsingleton.elim _ _, ?_⟩
  simp [unitaryOrbitGramSquareSum]

/-- A single genuine unitary orbit column has exactly zero error, not merely a zero expectation. -/
theorem singleton_orbit_gram (D : ℕ) (W : Fin 1 → Matrix (Fin D) (Fin D) ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix (Fin D) (Fin D) ℂ))
    (ψ : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) : unitaryOrbitGramError W ψ = 0 := by
  ext w v
  fin_cases w
  fin_cases v
  rw [unitaryOrbitGramError_apply W hW]
  simp

/-- The incomplete two-unitary family from the chaos regression has genuine Gram moment 2/3. -/
theorem two_unitary_orbit_moment (ψ₀ : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (∫ U, unitaryOrbitGramSquareSum signedUnitaryFamily
      (complexUnitarySphereAction (Fin 2) U ψ₀) ∂complexUnitaryHaar (Fin 2)) = (2:ℝ)/3 := by
  convert unitaryOrbitGramSquareSum_haar_moment signedUnitaryFamily signedUnitaryFamily_unitary
    (by simpa using signedUnitaryFamily_hilbertSchmidt) ψ₀ using 1
  norm_num

theorem two_unitary_orbit_tail (t : ℝ) (ht : 0<t)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    complexUnitaryHaar (Fin 2)
      {U | t < ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (unitaryOrbitGramError signedUnitaryFamily (complexUnitarySphereAction (Fin 2) U ψ₀))‖} ≤
      ENNReal.ofReal (2/(3*t^2)) := by
  convert unitaryOrbitGram_haar_tail signedUnitaryFamily signedUnitaryFamily_unitary
    (by simpa using signedUnitaryFamily_hilbertSchmidt) t ht ψ₀ using 1
  norm_num

/-- The m=1 tail is exactly zero for positive threshold. -/
theorem singleton_orbit_tail_zero (D : ℕ)
    (W : Fin 1 → Matrix (Fin D) (Fin D) ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix (Fin D) (Fin D) ℂ))
    (t : ℝ) (ht : 0<t) (ψ₀ : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    complexUnitaryHaar (Fin D)
      {U | t < ‖Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℂ)
        (unitaryOrbitGramError W (complexUnitarySphereAction (Fin D) U ψ₀))‖} = 0 := by
  simp only [singleton_orbit_gram D W hW, map_zero, norm_zero]
  simp [ht.not_gt]

end CertificationGaussian.Consumers
