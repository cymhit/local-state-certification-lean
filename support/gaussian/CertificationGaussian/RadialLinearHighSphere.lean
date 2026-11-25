import CertificationGaussian.RadialLinearHighTail
import CertificationGaussian.RadialHighSphere

noncomputable section
open MeasureTheory Matrix Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- The same actual scalar mean retains its original polynomial bound after linear truncation. -/
theorem radialLinearFirstHighWeights_mean_abs_le {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    |(∑ w : Fin n → K,radialLinearFirstHighWeights d n r ε lam k0 w)/(d:ℝ)^n|≤
      complementLambdaCoefficient d r lam*(n:ℝ)^r := by
  rw [abs_div,abs_of_nonneg (show (0:ℝ)≤(d:ℝ)^n by positivity)]
  calc
    _ ≤ (∑ w : Fin n → K,|radialLinearFirstHighWeights d n r ε lam k0 w|)/(d:ℝ)^n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ((d:ℝ)^n)⁻¹*∑ w : Fin n → K,|radialLinearFirstHighWeights d n r ε lam k0 w| := by ring
    _ ≤ complementLambda d n r lam := radialLinearFirstHighWeights_abs_mass d n r (by omega) ε lam k0 hcard
    _ ≤ _ := complementLambda_le_polynomial d n r hd hn lam

/-- The second mean keeps the exact factor2 and squared coefficients. -/
theorem radialLinearSecondHighWeights_mean_abs_le {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    |(∑ w : Fin n → K,radialLinearSecondHighWeights d n r ε lam k0 w)/(d:ℝ)^n|≤
      2*complementLambdaCoefficient d r (fun j => (lam j)^2)*(n:ℝ)^r := by
  simp only [radialLinearSecondHighWeights_eq,← Finset.mul_sum,mul_div_assoc,abs_mul,
    abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (radialLinearFirstHighWeights_mean_abs_le d n r hd hn ε (fun j => (lam j)^2) k0 hcard)
    (show (0:ℝ)≤2 by norm_num)

/-- First actual high sphere block on the actual Gaussian/radius good event. -/
theorem radialLinearFirstHigh_sphere_of_good_radius {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 2≤n) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hr : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹)
    (hg : ‖unitaryGaussianCentered
      (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d n r ε lam k0) x‖≤((n:ℝ)^3)⁻¹) :
    ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d n r ε lam k0)
      (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))‖≤
        (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ := by
  apply quditSphereCentered_of_good_radius d n r hn _ _ _
    (complementLambdaCoefficient_nonneg d r hd lam) x e₀ hr hg
  exact radialLinearFirstHighWeights_mean_abs_le d n r hd (by omega) ε lam k0 hcard

/-- The second high sphere block uses its true doubled squared-coefficient mean, on the same good radius event. -/
theorem radialLinearSecondHigh_sphere_of_good_radius {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 2≤n) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (hr : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹)
    (hg : ‖unitaryGaussianCentered
      (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearSecondHighWeights d n r ε lam k0) x‖≤((n:ℝ)^3)⁻¹) :
    ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearSecondHighWeights d n r ε lam k0)
      (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))‖≤
        (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ := by
  have hA := complementLambdaCoefficient_nonneg d r hd (fun j => (lam j)^2)
  have hm := radialLinearSecondHighWeights_mean_abs_le d n r hd (by omega) ε lam k0 hcard
  have h := quditSphereCentered_of_good_radius d n r hn _ _ _ (show 0≤2*complementLambdaCoefficient d r (fun j => (lam j)^2) by positivity)
    x e₀ hr hg hm
  convert h using 1
  ring

/-- The one common radius has an exponential bound, by the already proved stronger cubic bound. -/
theorem quditRadius_power_eventually_linear (d : ℕ) (hd : 2≤d) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,pairedGaussian (QuditIndex d n)
      {x | ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1|}≤
        ENNReal.ofReal (Real.exp (-(Real.log (d:ℝ)/4)*n)) := by
  have ha : 0<Real.log (d:ℝ)/4 := by
    have h := Real.log_pos (show (1:ℝ)<d by exact_mod_cast (show 1<d by omega))
    positivity
  filter_upwards [quditRadius_power_eventually_cubic hd k,eventually_ge_atTop 1] with n hc hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hcube : (n:ℝ)≤(n:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1≤3 by omega)
  have hs : {x | ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1|} ⊆
      {x | ((n:ℝ)^k)⁻¹≤ |gaussianRadius (QuditIndex d n) x-1|} := by
    intro x hx
    change ((n:ℝ)^k)⁻¹< |gaussianRadius (QuditIndex d n) x-1| at hx
    change ((n:ℝ)^k)⁻¹≤ |gaussianRadius (QuditIndex d n) x-1|
    exact hx.le
  exact ((measure_mono hs).trans hc).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith)))

/-- Common rate after transporting actual high Gaussian blocks with their single radius. -/
def radialLinearSphereRate (d : ℕ) (ε : ℝ) : ℝ :=
  min (radialLinearHighRate d ε/4) (Real.log (d:ℝ)/4)

theorem radialLinearSphereRate_pos (d : ℕ) (hd : 2≤d) (ε : ℝ) (hε : 0<ε)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) : 0<radialLinearSphereRate d ε := by
  have hr := radialLinearHighRate_pos d hd ε hε hgap
  have hl : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  apply lt_min <;> linarith

/-- Failure of either genuinely normalized, centered radial high block on the canonical complex sphere. -/
def radialLinearHighSphereBad {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  {ψ | (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹<
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearFirstHighWeights d n r ε lam k0) ψ‖ ∨
    (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹<
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearSecondHighWeights d n r ε lam k0) ψ‖}

theorem radialLinearHighSphereBad_measurable {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) :
    MeasurableSet (radialLinearHighSphereBad d n r ε lam W k0) := by
  unfold radialLinearHighSphereBad
  rw [Set.ofPred_or]
  apply MeasurableSet.union
  · exact (isOpen_lt continuous_const
      ((unitarySphereCentered_continuous _ _).comp continuous_subtype_val).norm).measurableSet
  · exact (isOpen_lt continuous_const
      ((unitarySphereCentered_continuous _ _).comp continuous_subtype_val).norm).measurableSet

/-- Actual canonical-sphere joint probability bound. The dimension cutoff is uniform over W; both errors use the same radius and Gaussian sample. -/
theorem radialLinearHigh_canonicalSphere_joint_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (radialLinearHighSphereBad d n r ε lam W k0) ≤
        ENNReal.ofReal (3*Real.exp (-radialLinearSphereRate d ε*n)) := by
  filter_upwards [radialLinearHigh_gaussian_joint_tail d r hd ε hε hhalf hgap lam k0 hcard,
    quditRadius_power_eventually_linear d hd (r+4),eventually_ge_atTop 2] with n hg hr hn
  intro W h0 hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex d n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z,hz⟩
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a1 := radialLinearFirstHighWeights d n r ε lam k0
  let a2 := radialLinearSecondHighWeights d n r ε lam k0
  let E : Set (Fin 2 × QuditIndex d n → ℝ) :=
    {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a1 x‖ ∨
      ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a2 x‖}
  let R : Set (Fin 2 × QuditIndex d n → ℝ) :=
    {x | ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|}
  have hm : Measurable (fun x : Fin 2 × QuditIndex d n → ℝ =>
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm (radialLinearHighSphereBad_measurable d n r ε lam W k0)]
  have hs : (fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) ⁻¹'
      radialLinearHighSphereBad d n r ε lam W k0 ⊆ E∪R := by
    intro x hx
    by_contra hnot
    have hb : ¬((((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a1 x‖ ∨
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered G a2 x‖) ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|) := hnot
    have hrad : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹ := le_of_not_gt (not_or.mp hb).2
    have h1 := radialLinearFirstHigh_sphere_of_good_radius d n r (by omega) hn ε lam k0 hcard W x e₀ hrad
      (le_of_not_gt (not_or.mp (not_or.mp hb).1).1)
    have h2 := radialLinearSecondHigh_sphere_of_good_radius d n r (by omega) hn ε lam k0 hcard W x e₀ hrad
      (le_of_not_gt (not_or.mp (not_or.mp hb).1).2)
    exact hx.elim (not_lt_of_ge h1) (not_lt_of_ge h2)
  have hg' : pairedGaussian (QuditIndex d n) E≤ENNReal.ofReal (2*Real.exp (-radialLinearSphereRate d ε*n)) :=
    (hg W h0 hW hHS).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (radialLinear_exp_rate_le n _ _ (min_le_left _ _)) (by norm_num : (0:ℝ)≤2)))
  have hr' : pairedGaussian (QuditIndex d n) R≤ENNReal.ofReal (Real.exp (-radialLinearSphereRate d ε*n)) :=
    hr.trans (ENNReal.ofReal_le_ofReal (radialLinear_exp_rate_le n _ _ (min_le_right _ _)))
  refine (measure_mono hs).trans ((measure_union_le E R).trans ((add_le_add hg' hr').trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The identical event under a genuine full-complex-unitary Haar orbit of any fixed initial unit vector. -/
theorem radialLinearHigh_haar_joint_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n)
        {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈radialLinearHighSphereBad d n r ε lam W k0} ≤
        ENNReal.ofReal (3*Real.exp (-radialLinearSphereRate d ε*n)) := by
  filter_upwards [radialLinearHigh_canonicalSphere_joint_tail d r hd ε hε hhalf hgap lam k0 hcard] with n hn
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have he := congrArg
    (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) =>
      μ (radialLinearHighSphereBad d n r ε lam W k0))
    (complexUnitaryHaar_orbit_map (QuditIndex d n) ψ)
  rw [Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right
    (radialLinearHighSphereBad_measurable d n r ε lam W k0)] at he
  have h := hn W h0 hW hHS
  rw [← he] at h
  exact h

end CertificationGaussian
