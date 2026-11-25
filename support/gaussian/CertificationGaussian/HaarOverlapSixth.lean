import CertificationGaussian.GaussianRadialSixth
import CertificationGaussian.ComplexGaussianWick
import CertificationGaussian.SphereComplexMoments
import CertificationGaussian.HaarBasisRecords
import CertificationGaussian.HaarCoordinateBeta

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators ComplexConjugate
namespace CertificationGaussian
variable (I : Type*) [Fintype I] [DecidableEq I]

/-- The sixth norm moment of the actual variance-one complex Gaussian coordinate. -/
theorem complexGaussian_coordinate_norm_sixth (i : I) :
    (∫ x, ‖complexCoordinate x i‖^6 ∂pairedGaussian I) = 6 := by
  have h := complexGaussian_same_coordinate_moment 3 i
  have he (z : ℂ) : star z^3*z^3 = ((‖z‖^6 : ℝ):ℂ) := by
    rw [← mul_pow,Complex.star_def,Complex.conj_mul']
    push_cast
    ring
  simp_rw [he] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

omit [DecidableEq I] in
/-- The canonical complex sphere transports real-valued expectations by the true real isometry. -/
theorem complexSphere_real_integral_eq_real (f : EuclideanSpace ℂ I → ℝ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, f ψ ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      ∫ ψ : sphere (0 : EuclideanSpace ℝ (Fin 2 × I)) 1,
        f (complexRealIsometry I ψ) ∂standardSphereMeasure (Fin 2 × I) := by
  rw [← sphereIsometry_canonical_map (complexRealIsometry I)]
  exact (sphereIsometry (complexRealIsometry I)).measurableEmbedding.integral_map _

omit [DecidableEq I] in
theorem complexRealIsometry_coordinate_norm_sixth (x : (Fin 2 × I) → ℝ) (i : I) :
    ‖complexRealIsometry I (WithLp.toLp 2 x) i‖^6 = 8*‖complexCoordinate x i‖^6 := by
  have h := congrArg (fun z : EuclideanSpace ℂ I => z i) (complexGaussianLift_eq I x)
  change complexCoordinate x i = (Real.sqrt 2)⁻¹ • complexRealIsometry I (WithLp.toLp 2 x) i at h
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [h,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),mul_pow]
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hsix : Real.sqrt (2:ℝ)^6=8 := by
    calc
      _ = (Real.sqrt (2:ℝ)^2)^3 := by ring
      _ = 8 := by rw [hsq]; norm_num
  field_simp
  rw [hsix]

theorem stdGaussian_complex_coordinate_sixth (i : I) :
    (∫ x : EuclideanSpace ℝ (Fin 2 × I), ‖complexRealIsometry I x i‖^6 ∂stdGaussian _) = 48 := by
  rw [stdGaussian_integral_eq_product]
  simp_rw [complexRealIsometry_coordinate_norm_sixth]
  rw [integral_const_mul]
  change 8*(∫ x, ‖complexCoordinate x i‖^6 ∂pairedGaussian I)=48
  rw [complexGaussian_coordinate_norm_sixth]
  norm_num

/-- The actual canonical complex-sphere coordinate sixth moment, with positive dimension. -/
theorem complexSphere_coordinate_norm_sixth [Nonempty I] (i : I) :
    (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, ‖ψ.val i‖^6
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
      6/((Fintype.card I:ℝ)*((Fintype.card I:ℝ)+1)*((Fintype.card I:ℝ)+2)) := by
  rw [complexSphere_real_integral_eq_real I (fun x => ‖x i‖^6)]
  have h := gaussian_homogeneous_integral (Fin 2 × I) 6
    (fun x => ‖complexRealIsometry I x i‖^6) (by
      intro r hr x
      rw [map_smul,PiLp.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow])
  rw [stdGaussian_complex_coordinate_sixth,stdGaussian_norm_sixth_moment] at h
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h
  have hD : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply (eq_div_iff (mul_pos (mul_pos hD (by positivity)) (by positivity)).ne').mpr
  nlinarith

/-- The concrete complex-unitary action preserves the complex inner product. -/
theorem complexUnitarySphereAction_inner (U : ComplexUnitary I)
    (x y : sphere (0 : EuclideanSpace ℂ I) 1) :
    inner ℂ (complexUnitarySphereAction I U x).val (complexUnitarySphereAction I U y).val =
      inner ℂ x.val y.val := by
  exact (Unitary.linearIsometryEquiv ⟨Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.val,
    Unitary.map_mem (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) U.property⟩).inner_map_map x.val y.val

/-- The squared overlap with any fixed unit vector has the beta law of a
coordinate. Haar invariance transports the fixed vector to a coordinate axis. -/
theorem complexSphere_squaredOverlap_beta [Nonempty I] (hd : 2 ≤ Fintype.card I)
    (b : sphere (0 : EuclideanSpace ℂ I) 1) :
    (canonicalSphereMeasure (EuclideanSpace ℂ I)).map
        (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 => ‖inner ℂ b.val ψ.val‖^2) =
      betaMeasure 1 ((Fintype.card I : ℝ) - 1) := by
  let i : I := Classical.arbitrary I
  obtain ⟨U, hU⟩ := complexUnitarySphereAction_transitive I (coordinateUnitVector I i) b
  rw [← haar_squaredCoordinate_beta I hd i]
  conv_lhs => rw [← complexUnitarySphereAction_canonical_map I U]
  rw [Measure.map_map (show Measurable (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
    ‖inner ℂ b.val ψ.val‖^2) by fun_prop)
    (complexUnitarySphereAction_continuous I).measurable.of_uncurry_left]
  congr 1
  funext ψ
  simp only [Function.comp_apply, ← hU, complexUnitarySphereAction_inner,
    coordinateUnitVector, EuclideanSpace.basisFun_inner]

/-- The sixth overlap moment is the third moment of the squared-overlap
beta law in dimensions at least two. -/
theorem complexSphere_overlap_sixth [Nonempty I]
    (b : sphere (0 : EuclideanSpace ℂ I) 1) :
    (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, ‖inner ℂ b.val ψ.val‖^6
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
      6/((Fintype.card I:ℝ)*((Fintype.card I:ℝ)+1)*((Fintype.card I:ℝ)+2)) := by
  by_cases hd : 2 ≤ Fintype.card I
  · have hb : 0 < (Fintype.card I : ℝ) - 1 := by
      have : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hd
      linarith
    have h := congrArg (fun μ : Measure ℝ => ∫ x, x^3 ∂μ) (complexSphere_squaredOverlap_beta I hd b)
    rw [integral_map (show Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
      ‖inner ℂ b.val ψ.val‖^2) by fun_prop).aemeasurable (by fun_prop),
      betaOne_third_moment _ hb] at h
    simpa only [← pow_mul, show 2*3=6 by decide, sub_add_cancel,
      show (Fintype.card I : ℝ)-1+2 = (Fintype.card I : ℝ)+1 by ring,
      show (Fintype.card I : ℝ)-1+3 = (Fintype.card I : ℝ)+2 by ring] using h
  let i : I := Classical.arbitrary I
  obtain ⟨U,hU⟩ := complexUnitarySphereAction_transitive I (coordinateUnitVector I i) b
  rw [← complexUnitarySphereAction_canonical_map I U,
    integral_map (complexUnitarySphereAction_continuous I).measurable.of_uncurry_left.aemeasurable
      (show Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
        ‖inner ℂ b.val ψ.val‖^6) by fun_prop).aestronglyMeasurable]
  simp_rw [← hU,complexUnitarySphereAction_inner]
  simpa only [coordinateUnitVector,EuclideanSpace.basisFun_inner] using
    complexSphere_coordinate_norm_sixth I i

/-- Each genuine Haar basis column has the same uniform sixth overlap moment. -/
theorem haar_column_overlap_sixth [Nonempty I]
    (b : sphere (0 : EuclideanSpace ℂ I) 1) (j : I) :
    (∫ U : ComplexUnitary I, ‖inner ℂ b.val
      (complexUnitarySphereAction I U (coordinateUnitVector I j)).val‖^6
      ∂complexUnitaryHaar I) =
      6/((Fintype.card I:ℝ)*((Fintype.card I:ℝ)+1)*((Fintype.card I:ℝ)+2)) := by
  have h := complexSphere_overlap_sixth I b
  rw [← complexUnitaryHaar_orbit_map I (coordinateUnitVector I j),
    integral_map (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right.aemeasurable
      (show Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
        ‖inner ℂ b.val ψ.val‖^6) by fun_prop).aestronglyMeasurable] at h
  exact h

/-- The genuine column vector retained by the full basis/outcome record. -/
def haarRecordedUnitVector (d : ℕ) [NeZero d]
    (ω : ComplexUnitary (Fin d) × Fin d) : sphere (0 : EuclideanSpace ℂ (Fin d)) 1 :=
  complexUnitarySphereAction (Fin d) ω.1 (coordinateUnitVector (Fin d) ω.2)

@[fun_prop] theorem haarRecordedUnitVector_continuous (d : ℕ) [NeZero d] :
    Continuous (haarRecordedUnitVector d) := by
  apply continuous_prod_of_discrete_right.mpr
  intro j
  change Continuous (fun U : ComplexUnitary (Fin d) =>
    complexUnitarySphereAction (Fin d) U (coordinateUnitVector (Fin d) j))
  exact (complexUnitarySphereAction_continuous (Fin d)).uncurry_right
    (coordinateUnitVector (Fin d) j)

theorem uniformFiniteOutcome_real_integral (d : ℕ) (f : Fin d → ℝ) :
    ∫ j, f j ∂uniformFiniteOutcome d = (d : ℝ)⁻¹ * ∑ j, f j := by
  rw [uniformFiniteOutcome,integral_smul_measure,integral_count]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]

/-- The overlap moment is for the complete Haar-basis/uniform-outcome records,
with the same probability used in the local readout tensors. -/
theorem haarBasisRecords_overlap_sixth (d : ℕ) [NeZero d]
    (b : sphere (0 : EuclideanSpace ℂ (Fin d)) 1) :
    (∫ ω, ‖inner ℂ b.val (haarRecordedUnitVector d ω).val‖^6 ∂haarBasisRecords d) =
      6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)) := by
  have hc : Continuous (fun ω => ‖inner ℂ b.val (haarRecordedUnitVector d ω).val‖^6) := by fun_prop
  have hi : Integrable (fun ω => ‖inner ℂ b.val (haarRecordedUnitVector d ω).val‖^6)
      (haarBasisRecords d) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [haarBasisRecords,integral_prod _ hi]
  simp_rw [uniformFiniteOutcome_real_integral]
  rw [integral_const_mul,integral_finsetSum]
  · simp_rw [haarRecordedUnitVector,haar_column_overlap_sixth]
    simp only [Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hd : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    rw [← mul_assoc,inv_mul_cancel₀ hd,one_mul]
  · intro j _
    have hcol : Continuous (fun U : ComplexUnitary (Fin d) =>
        ‖inner ℂ b.val (haarRecordedUnitVector d (U,j)).val‖^6) :=
      hc.comp (continuous_id.prodMk continuous_const)
    exact hcol.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The unit vector is the column used by the recorded rank-one projector. -/
theorem haarRecordedUnitVector_apply (d : ℕ) [NeZero d]
    (ω : ComplexUnitary (Fin d) × Fin d) (i : Fin d) :
    (haarRecordedUnitVector d ω).val i = ω.1.val i ω.2 :=
  complexUnitary_column (Fin d) ω.1 ω.2 i

theorem haarRecordedUnitVector_projector (d : ℕ) [NeZero d]
    (ω : ComplexUnitary (Fin d) × Fin d) (i j : Fin d) :
    recordedProjector d ω i j =
      (haarRecordedUnitVector d ω).val i*star ((haarRecordedUnitVector d ω).val j) := by
  simp only [haarRecordedUnitVector_apply,recordedProjector,columnProjector]

end CertificationGaussian
