import CertificationGaussian.RadialBinomialEntropy
import CertificationGaussian.RadialLowOrbit
import CertificationGaussian.RadialLinearCardinality
import CertificationGaussian.GramPolarCorrection

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Restriction of the original tensor family to the actual low labels at the fixed linear cutoff. -/
def radialLinearLowOrbitFamily (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    (radialLinearLowLabels ε n k0) → Matrix (QuditIndex d n) (QuditIndex d n) ℂ :=
  fun w => wickTensorMatrix (fun s => W (w.val s))

/-- Genuine unitarity is inherited by the actual restricted family. -/
theorem radialLinearLowOrbitFamily_unitary (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (hW : ∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ))
    (w : (radialLinearLowLabels ε n k0)) :
    radialLinearLowOrbitFamily d n ε W k0 w∈unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  radialTensorFamily_unitary d n W hW w.val

/-- Actual global HS orthogonality survives the low-label restriction without a surrogate dimension assumption. -/
theorem radialLinearLowOrbitFamily_hilbertSchmidt (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (w v : (radialLinearLowLabels ε n k0)) :
    Matrix.trace ((radialLinearLowOrbitFamily d n ε W k0 w)ᴴ*radialLinearLowOrbitFamily d n ε W k0 v)=
      if w=v then (Fintype.card (QuditIndex d n):ℂ) else 0 := by
  simpa only [radialLinearLowOrbitFamily,Subtype.val_inj] using radialTensorFamily_hilbertSchmidt d n W hHS w.val v.val

/-- The actual low-orbit Gram error event at the paper's n^-3 tolerance. -/
def radialLinearLowSphereBad (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  {ψ | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (𝕜:=ℂ)
    (unitaryOrbitGramError (radialLinearLowOrbitFamily d n ε W k0) ψ)‖}

theorem radialLinearLowSphereBad_measurable (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    MeasurableSet (radialLinearLowSphereBad d n ε W k0) :=
  unitaryOrbitGram_bad_measurable _ _

/-- The actual Gram counting factor is exponentially small at the fixed entropy-gap cutoff. -/
theorem radialLinearLow_gram_factor_eventually (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (k0 : K) (hcard : Fintype.card K=d^2)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) :
    ∀ᶠ n : ℕ in atTop,
      ((radialLinearLowLabels ε n k0).card:ℝ)*
        (((radialLinearLowLabels ε n k0).card:ℝ)-1)/((d:ℝ)^n+1)*(n:ℝ)^6 ≤
          Real.exp (-((Real.log (d:ℝ)-2*radialLinearEntropy d ε)/2)*n) := by
  filter_upwards [radialLinearLowLabels_polynomial_ratio_via_binomial_entropy d hd ε hε hhalf k0 hcard 1 6 2
    (by norm_num; linarith)] with n hn
  let m : ℝ := (radialLinearLowLabels ε n k0).card
  have hm : 0≤m := Nat.cast_nonneg _
  have hD : (0:ℝ)<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) _
  have hfrac : m*(m-1)/((d:ℝ)^n+1)≤m^2/(d:ℝ)^n := by
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith [mul_nonneg hm hD.le,sq_nonneg m]
  calc
    _ ≤ m^2/(d:ℝ)^n*(n:ℝ)^6 := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = (n:ℝ)^6*m^2/(d:ℝ)^n := by ring
    _ ≤ _ := by simpa only [one_mul,Nat.cast_ofNat] using hn

/-- Actual canonical-sphere low Gram probability, uniformly in the genuine local unitary HS family. -/
theorem radialLinearLow_canonicalSphere_tail (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (k0 : K) (hcard : Fintype.card K=d^2)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (radialLinearLowSphereBad d n ε W k0)≤
        ENNReal.ofReal (Real.exp (-((Real.log (d:ℝ)-2*radialLinearEntropy d ε)/2)*n)) := by
  filter_upwards [radialLinearLow_gram_factor_eventually d hd ε hε hhalf k0 hcard hgap,eventually_ge_atTop 1] with n hf hn
  intro W hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h := unitaryOrbitGram_sphere_tail (radialLinearLowOrbitFamily d n ε W k0)
    (radialLinearLowOrbitFamily_unitary d n ε W k0 hW)
    (radialLinearLowOrbitFamily_hilbertSchmidt d n ε W k0 hHS) (((n:ℝ)^3)⁻¹) (by positivity)
  have he : ((Fintype.card ↥(radialLinearLowLabels ε n k0):ℝ)*
      ((Fintype.card ↥(radialLinearLowLabels ε n k0):ℝ)-1))/
      (((Fintype.card (QuditIndex d n):ℝ)+1)*(((n:ℝ)^3)⁻¹)^2)=
      ((radialLinearLowLabels ε n k0).card:ℝ)*
        (((radialLinearLowLabels ε n k0).card:ℝ)-1)/((d:ℝ)^n+1)*(n:ℝ)^6 := by
    simp only [Fintype.card_coe,qudit_card,Nat.cast_pow]
    field_simp
  exact h.trans (ENNReal.ofReal_le_ofReal (he.trans_le hf))

/-- On the very same low Gram good event the actual CFC correction has orthonormal columns and small conjugation error. -/
theorem radialLinearLow_polar_on_good_event (d n : ℕ) (ε : ℝ) (hn : 2≤n)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (hg : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (unitaryOrbitGramError (radialLinearLowOrbitFamily d n ε W k0) ψ)‖≤((n:ℝ)^3)⁻¹) :
    let V := unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ
    let Q := matrixPolarCorrection V
    Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖≤((n:ℝ)^3)⁻¹ ∧
      (∀ x,‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
      (∀ A,‖V*A*Vᴴ-Q*A*Qᴴ‖≤3*‖A‖*((n:ℝ)^3)⁻¹) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have ht : ((n:ℝ)^3)⁻¹<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hn1 (by omega))
  dsimp only
  have h := matrixPolarCorrection_threshold (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ) ht hg
  exact ⟨h.1,h.2.1,rectangularEuclideanCLM_norm_map_of_gram _ h.1,
    fun A => matrixPolarCorrection_conjugation_le _ A ht hg⟩


/-- The same exponentially rare actual Gram event under genuine full complex Haar sampling. -/
theorem radialLinearLow_haar_tail (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (k0 : K) (hcard : Fintype.card K=d^2)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialLinearLowSphereBad d n ε W k0}≤
        ENNReal.ofReal (Real.exp (-((Real.log (d:ℝ)-2*radialLinearEntropy d ε)/2)*n)) := by
  filter_upwards [radialLinearLow_canonicalSphere_tail d hd ε hε hhalf k0 hcard hgap] with n hn
  intro W hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have h := hn W hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex d n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right
      (radialLinearLowSphereBad_measurable d n ε W k0)] at h
  exact h

end CertificationGaussian
