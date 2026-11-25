import CertificationGaussian.RadialHighSphere
import CertificationGaussian.GramPolarCorrection

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Restriction of the original tensor family to the actual low labels at the original cutoff. -/
def radialLowOrbitFamily (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    (radialLowLabels (S:=Fin n) d r k0) → Matrix (QuditIndex d n) (QuditIndex d n) ℂ :=
  fun w => wickTensorMatrix (fun s => W (w.val s))

/-- Genuine unitarity is inherited by the actual restricted family. -/
theorem radialLowOrbitFamily_unitary (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (hW : ∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ))
    (w : (radialLowLabels (S:=Fin n) d r k0)) :
    radialLowOrbitFamily d n r W k0 w∈unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  radialTensorFamily_unitary d n W hW w.val

/-- Actual global HS orthogonality survives the low-label restriction without a surrogate dimension assumption. -/
theorem radialLowOrbitFamily_hilbertSchmidt (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (w v : (radialLowLabels (S:=Fin n) d r k0)) :
    Matrix.trace ((radialLowOrbitFamily d n r W k0 w)ᴴ*radialLowOrbitFamily d n r W k0 v)=
      if w=v then (Fintype.card (QuditIndex d n):ℂ) else 0 := by
  simpa only [radialLowOrbitFamily,Subtype.val_inj] using radialTensorFamily_hilbertSchmidt d n W hHS w.val v.val

/-- The actual low-orbit Gram error event at the paper's n^-3 tolerance. -/
def radialLowSphereBad (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  {ψ | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (𝕜:=ℂ)
    (unitaryOrbitGramError (radialLowOrbitFamily d n r W k0) ψ)‖}

theorem radialLowSphereBad_measurable (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    MeasurableSet (radialLowSphereBad d n r W k0) :=
  unitaryOrbitGram_bad_measurable _ _

/-- The true low-label counting factor in the already proved actual Gram tail is eventually below n^-8. -/
theorem radialLow_gram_factor_eventually (d r : ℕ) (hd : 2≤d) (k0 : K) :
    ∀ᶠ n : ℕ in atTop,
      ((radialLowLabels (S:=Fin n) d r k0).card:ℝ)*
        (((radialLowLabels (S:=Fin n) d r k0).card:ℝ)-1)/((d:ℝ)^n+1)*(n:ℝ)^6 ≤
          ((n:ℝ)^8)⁻¹ := by
  filter_upwards [radialLowLabels_polynomial_ratio_inverse d r hd k0 1 6 2 8] with n hn
  let m : ℝ := (radialLowLabels (S:=Fin n) d r k0).card
  have hm : 0≤m := Nat.cast_nonneg _
  have hD : (0:ℝ)<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) _
  have hfrac : m*(m-1)/((d:ℝ)^n+1)≤m^2/(d:ℝ)^n := by
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith [mul_nonneg hm hD.le,sq_nonneg m]
  calc
    _ ≤ m^2/(d:ℝ)^n*(n:ℝ)^6 := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = (n:ℝ)^6*m^2/(d:ℝ)^n := by ring
    _ ≤ _ := by simpa only [one_mul] using hn

/-- Actual canonical-sphere low Gram probability, uniformly in the genuine local unitary HS family. -/
theorem radialLow_canonicalSphere_tail (d r : ℕ) (hd : 2≤d) (k0 : K) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (radialLowSphereBad d n r W k0)≤
        ENNReal.ofReal (((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialLow_gram_factor_eventually d r hd k0,eventually_ge_atTop 1] with n hf hn
  intro W hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h := unitaryOrbitGram_sphere_tail (radialLowOrbitFamily d n r W k0)
    (radialLowOrbitFamily_unitary d n r W k0 hW)
    (radialLowOrbitFamily_hilbertSchmidt d n r W k0 hHS) (((n:ℝ)^3)⁻¹) (by positivity)
  have he : ((Fintype.card ↥(radialLowLabels (S:=Fin n) d r k0):ℝ)*
      ((Fintype.card ↥(radialLowLabels (S:=Fin n) d r k0):ℝ)-1))/
      (((Fintype.card (QuditIndex d n):ℝ)+1)*(((n:ℝ)^3)⁻¹)^2)=
      ((radialLowLabels (S:=Fin n) d r k0).card:ℝ)*
        (((radialLowLabels (S:=Fin n) d r k0).card:ℝ)-1)/((d:ℝ)^n+1)*(n:ℝ)^6 := by
    simp only [Fintype.card_coe,qudit_card,Nat.cast_pow]
    field_simp
  exact h.trans (ENNReal.ofReal_le_ofReal (he.trans_le hf))

/-- On the very same low Gram good event the actual CFC correction has orthonormal columns and small conjugation error. -/
theorem radialLow_polar_on_good_event (d n r : ℕ) (hn : 2≤n)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (hg : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (unitaryOrbitGramError (radialLowOrbitFamily d n r W k0) ψ)‖≤((n:ℝ)^3)⁻¹) :
    let V := unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ
    let Q := matrixPolarCorrection V
    Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖≤((n:ℝ)^3)⁻¹ ∧
      (∀ x,‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
      (∀ A,‖V*A*Vᴴ-Q*A*Qᴴ‖≤3*‖A‖*((n:ℝ)^3)⁻¹) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have ht : ((n:ℝ)^3)⁻¹<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hn1 (by omega))
  dsimp only
  have h := matrixPolarCorrection_threshold (unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ) ht hg
  exact ⟨h.1,h.2.1,rectangularEuclideanCLM_norm_map_of_gram _ h.1,
    fun A => matrixPolarCorrection_conjugation_le _ A ht hg⟩

/-- The two high errors and low Gram error are events under the same canonical sphere law. -/
theorem radialHighLow_canonicalSphere_joint_tail (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0)≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) := by
  have hC := (radialHighGaussianConstant_pos d r hd lam).le
  have hC2 := (radialHighGaussianConstant_pos d r hd (fun j => (lam j)^2)).le
  filter_upwards [radialHigh_canonicalSphere_joint_tail d r hd lam k0 hcard,
    radialLow_canonicalSphere_tail d r hd k0] with n hh hl
  intro W h0 hW hHS
  refine (measure_union_le _ _).trans ((add_le_add (hh W h0 hW hHS) (hl W hW hHS)).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The identical high/low joint event under actual full Haar sampling, uniformly over the initial vector. -/
theorem radialHighLow_haar_joint_tail (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0}≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialHighLow_canonicalSphere_joint_tail d r hd lam k0 hcard] with n hn
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hm := (radialHighSphereBad_measurable d n r lam W k0).union
    (radialLowSphereBad_measurable d n r W k0)
  have h := hn W h0 hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex d n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm] at h
  exact h

end CertificationGaussian
