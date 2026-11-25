import CertificationGaussian.UnitarySphereConjugation
import CertificationGaussian.RadialHighTail

noncomputable section
open MeasureTheory Matrix Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- Deterministic normalization uses the existing single radius and the actual weight mean, with no independence assumption. -/
theorem quditSphereCentered_of_good_radius {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hn : 2≤n) (W : K → Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (a : K → ℝ) (A : ℝ) (hA : 0≤A) (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hr : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹)
    (hg : ‖unitaryGaussianCentered W a x‖≤((n:ℝ)^3)⁻¹)
    (hm : |(∑ w,a w)/(d:ℝ)^n|≤A*(n:ℝ)^r) :
    ‖unitarySphereCentered W a (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))‖≤
      (2+2*A)*((n:ℝ)^3)⁻¹ := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hh := quditReadout_good_radius hn r x hr
  have h := unitarySphereCentered_direction_norm_le W a x hh.1 e₀
  simp only [qudit_card,Nat.cast_pow] at h
  rw [abs_of_nonneg hh.2.1] at h
  have h1 := mul_le_mul hh.2.2.1 hg (norm_nonneg (unitaryGaussianCentered W a x)) (show (0:ℝ)≤2 by norm_num)
  have h2 := mul_le_mul hh.2.2.2 hm (abs_nonneg ((∑ w,a w)/(d:ℝ)^n))
    (show (0:ℝ)≤2*((n:ℝ)^(r+4))⁻¹ by positivity)
  have he : 2*((n:ℝ)^(r+4))⁻¹*(A*(n:ℝ)^r)=2*A*((n:ℝ)^4)⁻¹ := by
    rw [pow_add]
    field_simp
  have hi : ((n:ℝ)^4)⁻¹≤((n:ℝ)^3)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hn0 3)
      (pow_le_pow_right₀ hn1 (show 3≤4 by omega))
  refine h.trans ((add_le_add h1 h2).trans ?_)
  rw [he]
  calc
    _ ≤ 2*((n:ℝ)^3)⁻¹+2*A*((n:ℝ)^3)⁻¹ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hi (by positivity))
    _ = _ := by ring

/-- First actual high sphere block on the actual Gaussian/radius good event. -/
theorem radialFirstHigh_sphere_of_good_radius {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 2≤n) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hr : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹)
    (hg : ‖unitaryGaussianCentered
      (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r lam k0) x‖≤((n:ℝ)^3)⁻¹) :
    ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r lam k0)
      (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))‖≤
        (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ := by
  apply quditSphereCentered_of_good_radius d n r hn _ _ _
    (complementLambdaCoefficient_nonneg d r hd lam) x e₀ hr hg
  simpa only [Fintype.card_fin] using radialFirstHighWeights_mean_abs_le
    (S:=Fin n) d r hd (by simp; omega) lam k0 hcard

/-- The second high sphere block uses its true doubled squared-coefficient mean, on the same good radius event. -/
theorem radialSecondHigh_sphere_of_good_radius {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 2≤n) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hr : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹)
    (hg : ‖unitaryGaussianCentered
      (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r lam k0) x‖≤((n:ℝ)^3)⁻¹) :
    ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r lam k0)
      (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))‖≤
        (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ := by
  have hA := complementLambdaCoefficient_nonneg d r hd (fun j => (lam j)^2)
  have hm := radialSecondHighWeights_mean_abs_le (S:=Fin n) d r hd (by simp; omega) lam k0 hcard
  simp only [Fintype.card_fin] at hm
  have h := quditSphereCentered_of_good_radius d n r hn _ _ _ (show 0≤2*complementLambdaCoefficient d r (fun j => (lam j)^2) by positivity)
    x e₀ hr hg hm
  convert h using 1
  ring

/-- The single common-radius failure is eventually below every inverse power, by its already proved cubic tail. -/
theorem quditRadius_power_eventually_inverse (d : ℕ) (hd : 2≤d) (k s : ℕ) :
    ∀ᶠ n : ℕ in atTop,pairedGaussian (QuditIndex d n)
      {x | ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1|}≤ENNReal.ofReal (((n:ℝ)^s)⁻¹) := by
  have ha : 0<Real.log (d:ℝ)/4 := by
    have h := Real.log_pos (show (1:ℝ)<d by exact_mod_cast (show 1<d by omega))
    positivity
  filter_upwards [quditRadius_power_eventually_cubic hd k,
    eventually_exp_neg_le_inverse_pow ha s,eventually_ge_atTop 1] with n hc he hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hcube : (n:ℝ)≤(n:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1≤3 by omega)
  have hs : {x | ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ⊆
      {x | ((n:ℝ)^k)⁻¹≤ |gaussianRadius (QuditIndex d n) x-1|} := by
    intro x hx
    change ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1| at hx
    change ((n:ℝ)^k)⁻¹≤ |gaussianRadius (QuditIndex d n) x-1|
    exact hx.le
  have hexp : Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)^3)≤Real.exp (-(Real.log (d:ℝ)/4)*n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact ((measure_mono hs).trans hc).trans (ENNReal.ofReal_le_ofReal (hexp.trans he))

/-- Failure of either genuinely normalized, centered radial high block on the canonical complex sphere. -/
def radialHighSphereBad {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  {ψ | (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹<
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialFirstHighWeights d r lam k0) ψ‖ ∨
    (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹<
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialSecondHighWeights d r lam k0) ψ‖}

theorem radialHighSphereBad_measurable {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    MeasurableSet (radialHighSphereBad d n r lam W k0) := by
  unfold radialHighSphereBad
  rw [Set.ofPred_or]
  apply MeasurableSet.union
  · exact (isOpen_lt continuous_const
      ((unitarySphereCentered_continuous _ _).comp continuous_subtype_val).norm).measurableSet
  · exact (isOpen_lt continuous_const
      ((unitarySphereCentered_continuous _ _).comp continuous_subtype_val).norm).measurableSet

/-- Actual canonical-sphere joint probability bound. The dimension cutoff is uniform over W; both errors use the same radius and Gaussian sample. -/
theorem radialHigh_canonicalSphere_joint_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (radialHighSphereBad d n r lam W k0) ≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+1)*((n:ℝ)^8)⁻¹) := by
  have hC := (radialHighGaussianConstant_pos d r hd lam).le
  have hC2 := (radialHighGaussianConstant_pos d r hd (fun j => (lam j)^2)).le
  filter_upwards [radialHigh_gaussian_joint_tail d r hd lam k0 hcard,
    quditRadius_power_eventually_inverse d hd (r+4) 8,eventually_ge_atTop 2] with n hg hr hn
  intro W h0 hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex d n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z,hz⟩
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a1 := radialFirstHighWeights (S:=Fin n) d r lam k0
  let a2 := radialSecondHighWeights (S:=Fin n) d r lam k0
  let E : Set (Fin 2 × QuditIndex d n → ℝ) :=
    {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a1 x‖ ∨
      ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a2 x‖}
  let R : Set (Fin 2 × QuditIndex d n → ℝ) :=
    {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|}
  have hm : Measurable (fun x : Fin 2 × QuditIndex d n → ℝ =>
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm (radialHighSphereBad_measurable d n r lam W k0)]
  have hs : (fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) ⁻¹'
      radialHighSphereBad d n r lam W k0 ⊆ E∪R := by
    intro x hx
    by_contra hnot
    have hb : ¬((((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a1 x‖ ∨
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a2 x‖) ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|) := hnot
    have hrad : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹ := le_of_not_gt (not_or.mp hb).2
    have h1 := radialFirstHigh_sphere_of_good_radius d n r (by omega) hn lam k0 hcard W x e₀ hrad
      (le_of_not_gt (not_or.mp (not_or.mp hb).1).1)
    have h2 := radialSecondHigh_sphere_of_good_radius d n r (by omega) hn lam k0 hcard W x e₀ hrad
      (le_of_not_gt (not_or.mp (not_or.mp hb).1).2)
    exact hx.elim (not_lt_of_ge h1) (not_lt_of_ge h2)
  refine (measure_mono hs).trans ((measure_union_le E R).trans
    ((add_le_add (hg W h0 hW hHS) hr).trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The identical event under a genuine full-complex-unitary Haar orbit of any fixed initial unit vector. -/
theorem radialHigh_haar_joint_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n)
        {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈radialHighSphereBad d n r lam W k0} ≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+1)*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialHigh_canonicalSphere_joint_tail d r hd lam k0 hcard] with n hn
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have he := congrArg
    (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) =>
      μ (radialHighSphereBad d n r lam W k0))
    (complexUnitaryHaar_orbit_map (QuditIndex d n) ψ)
  rw [Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right
    (radialHighSphereBad_measurable d n r lam W k0)] at he
  have h := hn W h0 hW hHS
  rw [← he] at h
  exact h

end CertificationGaussian
