import CertificationGaussian.SphereTransport
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.LIntegral

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal
namespace CertificationGaussian

/-- The actual finite complex unitary matrix group with its inherited topology. -/
abbrev ComplexUnitary (I : Type*) [Fintype I] [DecidableEq I] :=
  ↥(unitary (Matrix I I ℂ))

instance complexUnitary_compact (I : Type*) [Fintype I] [DecidableEq I] :
    CompactSpace (ComplexUnitary I) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_pi_infinite (fun _ : I =>
    isCompact_pi_infinite (fun _ : I => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset
    (isClosed_unitary (R := Matrix I I ℂ))
  intro U hU i j
  simpa only [mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hU i j

instance complexUnitary_secondCountable (I : Type*) [Fintype I] [DecidableEq I] :
    SecondCountableTopology (ComplexUnitary I) := by
  let : SecondCountableTopology (Matrix I I ℂ) :=
    inferInstanceAs (SecondCountableTopology (I → I → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology (unitary (Matrix I I ℂ) : Set (Matrix I I ℂ))

section CompactHaar
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [SecondCountableTopology G]

/-- Haar measure normalized on the entire compact group. -/
def compactHaarProbability : Measure G := Measure.haarMeasure ⊤

instance compactHaarProbability_probability : IsProbabilityMeasure (compactHaarProbability G) where
  measure_univ := by
    change Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G) univ = 1
    rw [← TopologicalSpace.PositiveCompacts.coe_top]
    exact Measure.haarMeasure_self

instance compactHaarProbability_isHaar : (compactHaarProbability G).IsHaarMeasure := by
  unfold compactHaarProbability
  infer_instance

instance compactHaarProbability_left : (compactHaarProbability G).IsMulLeftInvariant := by
  unfold compactHaarProbability
  infer_instance

instance compactHaarProbability_right : (compactHaarProbability G).IsMulRightInvariant := by
  constructor
  intro g
  exact ((Measure.haarMeasure_eq_iff ⊤ ((compactHaarProbability G).map (· * g))).2
    (by simp)).symm
end CompactHaar

/-- Double averaging identifies an invariant probability with a transitive Haar orbit.
The action and invariance assumptions are discharged by the concrete matrix action below. -/
theorem haar_orbit_eq_of_transitive
    {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : G → X → X) (hA : Measurable (Function.uncurry A))
    (hmul : ∀ g h x, A (g * h) x = A g (A h x))
    (hinv : ∀ g, ν.map (A g) = ν) (x₀ : X)
    (htrans : ∀ x, ∃ g, A g x₀ = x) :
    (compactHaarProbability G).map (fun g => A g x₀) = ν := by
  ext s hs
  let f : X → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hconst (x : X) :
      ∫⁻ g, f (A g x) ∂compactHaarProbability G =
        ∫⁻ g, f (A g x₀) ∂compactHaarProbability G := by
    obtain ⟨h, rfl⟩ := htrans x
    simp_rw [← hmul]
    exact lintegral_mul_right_eq_self (fun g => f (A g x₀)) h
  calc
    _ = ∫⁻ g, f (A g x₀) ∂compactHaarProbability G := by
      rw [Measure.map_apply hA.of_uncurry_right hs]
      simpa only [f, one_mul] using
        (lintegral_indicator_const_comp hA.of_uncurry_right hs (1 : ℝ≥0∞)).symm
    _ = ∫⁻ x, ∫⁻ g, f (A g x) ∂compactHaarProbability G ∂ν := by
      simp_rw [hconst]
      simp
    _ = ∫⁻ g, ∫⁻ x, f (A g x) ∂ν ∂compactHaarProbability G :=
      lintegral_lintegral_swap (hf.comp (hA.comp measurable_swap)).aemeasurable
    _ = ∫⁻ _g, ν s ∂compactHaarProbability G := by
      congr 1
      funext g
      rw [← lintegral_map hf hA.of_uncurry_left, hinv]
      simp [f, hs]
    _ = ν s := by simp

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- The actual complex unitary matrix action on the unit sphere. -/
def complexUnitarySphereAction (U : ComplexUnitary I)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) : sphere (0 : EuclideanSpace ℂ I) 1 :=
  sphereIsometry (matrixUnitaryRealIsometry U.val U.property) ψ

@[simp] theorem complexUnitarySphereAction_coe (U : ComplexUnitary I)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (complexUnitarySphereAction I U ψ : EuclideanSpace ℂ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.val ψ := rfl

theorem complexUnitarySphereAction_continuous :
    Continuous (Function.uncurry (complexUnitarySphereAction I)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ComplexUnitary I × sphere (0 : EuclideanSpace ℂ I) 1 =>
    Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) p.1.val p.2.val)
  fun_prop

theorem complexUnitarySphereAction_mul (U V : ComplexUnitary I)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    complexUnitarySphereAction I (U * V) ψ =
      complexUnitarySphereAction I U (complexUnitarySphereAction I V ψ) := by
  apply Subtype.ext
  change Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.val * V.val) ψ =
    Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.val (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) V.val ψ)
  rw [map_mul]
  rfl

theorem complexUnitarySphereAction_canonical_map (U : ComplexUnitary I) :
    (canonicalSphereMeasure (EuclideanSpace ℂ I)).map (complexUnitarySphereAction I U) =
      canonicalSphereMeasure (EuclideanSpace ℂ I) :=
  sphereIsometry_canonical_map (matrixUnitaryRealIsometry U.val U.property)

omit [DecidableEq I] in
/-- A prescribed unit vector extends to a complex orthonormal basis at any fixed index. -/
theorem exists_complex_basis_at (i₀ : I) (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ∃ b : OrthonormalBasis I ℂ (EuclideanSpace ℂ I), b i₀ = ψ := by
  have hψ : ‖(ψ : EuclideanSpace ℂ I)‖ = 1 := mem_sphere_zero_iff_norm.mp ψ.property
  have ho : Orthonormal ℂ (({i₀} : Set I).domRestrict (fun _ : I => (ψ : EuclideanSpace ℂ I))) :=
    ⟨fun _ => hψ, Subsingleton.pairwise⟩
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb i₀ (mem_singleton i₀)⟩

/-- Transitivity is by complex linear unitary matrices, not by the larger real orthogonal group. -/
theorem complexUnitarySphereAction_transitive [Nonempty I]
    (ψ φ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ∃ U : ComplexUnitary I, complexUnitarySphereAction I U ψ = φ := by
  let i₀ : I := Classical.arbitrary I
  obtain ⟨b, hb⟩ := exists_complex_basis_at I i₀ ψ
  obtain ⟨c, hc⟩ := exists_complex_basis_at I i₀ φ
  let e : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I := b.repr.trans c.repr.symm
  have he : e (ψ : EuclideanSpace ℂ I) = φ := by
    rw [← hb, ← hc]
    simp [e]
  let C : ↥(unitary (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) :=
    Unitary.linearIsometryEquiv.symm e
  let U : ComplexUnitary I :=
    ⟨(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm C.val,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm C.property⟩
  refine ⟨U, ?_⟩
  apply Subtype.ext
  change Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
    ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm C.val) ψ = φ
  rw [StarAlgEquiv.apply_symm_apply]
  exact he

/-- Normalized Haar measure on the actual full complex unitary matrix group. -/
def complexUnitaryHaar : Measure (ComplexUnitary I) := compactHaarProbability (ComplexUnitary I)

instance complexUnitaryHaar_isHaar : (complexUnitaryHaar I).IsHaarMeasure :=
  compactHaarProbability_isHaar _

instance complexUnitaryHaar_probability : IsProbabilityMeasure (complexUnitaryHaar I) :=
  compactHaarProbability_probability _

/-- The full complex-unitary Haar orbit is exactly canonical normalized sphere area. -/
theorem complexUnitaryHaar_orbit_map [Nonempty I]
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (complexUnitaryHaar I).map (fun U => complexUnitarySphereAction I U ψ) =
      canonicalSphereMeasure (EuclideanSpace ℂ I) :=
  haar_orbit_eq_of_transitive _ (complexUnitarySphereAction I)
    (complexUnitarySphereAction_continuous I).measurable
    (complexUnitarySphereAction_mul I) (complexUnitarySphereAction_canonical_map I) ψ
    (complexUnitarySphereAction_transitive I ψ)

/-- The actual normalized paired Gaussian and the actual complex-unitary Haar orbit agree. -/
theorem complexGaussian_direction_eq_haar_orbit [Nonempty I]
    (e₀ ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (pairedGaussian I).map (fun x => sphereDirection e₀ (complexGaussianLift I x)) =
      (complexUnitaryHaar I).map (fun U => complexUnitarySphereAction I U ψ) := by
  rw [complexGaussian_direction_map, complexUnitaryHaar_orbit_map]

end CertificationGaussian
