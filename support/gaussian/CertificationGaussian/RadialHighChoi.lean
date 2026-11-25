import CertificationGaussian.RadialLowAsymptotics
import CertificationGaussian.RadialBellChoi
import CertificationGaussian.TensorUnitaryNet
import CertificationGaussian.TensorReadoutFactorization

noncomputable section
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- The already existing tensor matrix of actual local unitaries is a genuine global unitary. -/
theorem radialTensorFamily_unitary (d n : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) (w : Fin n → K) :
    wickTensorMatrix (fun s => W (w s))∈unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := by
  exact tensorUnitaryMatrix_unitary d n (fun s => ⟨W (w s),hW (w s)⟩)

omit [Fintype K] in
/-- The same true tensor family has the required global Hilbert-Schmidt normalization. -/
theorem radialTensorFamily_hilbertSchmidt (d n : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (w v : Fin n → K) :
    Matrix.trace ((wickTensorMatrix (fun s => W (w s)))ᴴ*wickTensorMatrix (fun s => W (v s)))=
      if w=v then (Fintype.card (QuditIndex d n):ℂ) else 0 := by
  have he : (wickTensorMatrix (fun s => W (w s)))ᴴ=wickTensorMatrix (fun s => (W (w s))ᴴ) := by
    ext x y
    simp only [Matrix.conjTranspose_apply,wickTensorMatrix,star_prod]
  rw [he,wickTensorMatrix_mul,wickTensorMatrix_trace]
  simp_rw [hHS]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← funext_iff,qudit_card,Nat.cast_pow]

/-- The scalar right side of the actual first Choi bound. -/
def radialChoiTail (d n r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (r+1),|lam j.val| * (n.choose j.val:ℝ)*(2/(d+1:ℝ))^(n-j.val)

/-- A fixed polynomial times one strict geometric factor controls the actual Choi tail. -/
theorem radialChoiTail_le_polynomial (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (hr : r≤n)
    (lam : ℕ → ℝ) : radialChoiTail d n r lam ≤
      (∑ j : Fin (r+1),|lam j.val|)*(n:ℝ)^r*(2/(d+1:ℝ))^(n-r) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hq0 : (0:ℝ)≤2/(d+1:ℝ) := by positivity
  have hq1 : (2:ℝ)/(d+1:ℝ)≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (show 2≤d+1 by omega))
  unfold radialChoiTail
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hj : j.val≤r := Nat.le_of_lt_succ j.isLt
  have hc : (n.choose j.val:ℝ)≤(n:ℝ)^r := by
    calc
      _ ≤ (n:ℝ)^j.val := by exact_mod_cast Nat.choose_le_pow n j.val
      _ ≤ _ := pow_le_pow_right₀ hn1 hj
  have hp : (2/(d+1:ℝ))^(n-j.val)≤(2/(d+1:ℝ))^(n-r) :=
    pow_le_pow_of_le_one hq0 hq1 (by omega)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) hp (pow_nonneg hq0 _)
    (mul_nonneg (abs_nonneg _) (by positivity))

/-- The genuine full Choi tail eventually beats any inverse power when d>=2. -/
theorem radialChoiTail_eventually_inverse (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop,radialChoiTail d n r lam≤((n:ℝ)^s)⁻¹ := by
  have hq0 : (0:ℝ)<2/(d+1:ℝ) := by positivity
  have hq1 : (2:ℝ)/(d+1:ℝ)<1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast (show 2<d+1 by omega))
  have ha : 0< -(Real.log (2/(d+1:ℝ))/2) := by linarith [Real.log_neg hq0 hq1]
  filter_upwards [eventually_polynomial_geometric_shift (∑ j : Fin (r+1),|lam j.val|) r r hq0 hq1,
    eventually_exp_neg_le_inverse_pow ha s,eventually_ge_atTop (max 1 r)] with n hg he hn
  have h := (radialChoiTail_le_polynomial d n r (by omega) (by omega) (by omega) lam).trans hg
  exact h.trans (by simpa only [neg_neg] using he)

/-- Exact finite truncation estimate for the actual original radial Bell matrix, before asymptotic absorption. -/
theorem radialFirstHigh_bell_partialTranspose_le (d r n : ℕ) (hd : 0<d) (lam : ℕ → ℝ)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hW : ∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ))
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) {C : ℝ} (hC : 0≤C)
    (hmax : ∀ w : ℕ,|radialFirstCoefficient d r lam w|≤C) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
      (weightedBellMatrix (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialFirstHighWeights d r lam k0)))‖ ≤
      radialChoiTail d n r lam+(radialLowLabels (S:=Fin n) d r k0).card*C/(d:ℝ)^n := by
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := fun w : Fin n → K => radialFirstCoefficient d r lam (radialBellSupport k0 w).card
  have hGa : ∀ w,G w∈unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := radialTensorFamily_unitary d n W hW
  have ha : ‖a‖≤C := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro w
    exact hmax (radialBellSupport k0 w).card
  have hrem := weightedBell_partialTranspose_remove_card_bound G a hGa (radialLowLabels (S:=Fin n) d r k0)
  rw [← radialFirstHighWeights_remove] at hrem
  simp only [qudit_card,Nat.cast_pow,Matrix.l2_opNorm_toEuclideanCLM] at hrem
  have hrem' : ‖partialTransposeFirst (weightedBellMatrix G a)-
      partialTransposeFirst (weightedBellMatrix G (radialFirstHighWeights d r lam k0))‖ ≤
      (radialLowLabels (S:=Fin n) d r k0).card*C/(d:ℝ)^n := hrem.trans (by gcongr)
  have hfull := radialFirstCoefficient_bell_partialTranspose_bound (S:=Fin n) d hd W k0 h0 hHS hcard r lam
  simp only [Matrix.l2_opNorm_toEuclideanCLM,Fintype.card_fin] at hfull
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  have he : partialTransposeFirst (weightedBellMatrix G (radialFirstHighWeights d r lam k0))=
      partialTransposeFirst (weightedBellMatrix G a)-
        (partialTransposeFirst (weightedBellMatrix G a)-partialTransposeFirst (weightedBellMatrix G (radialFirstHighWeights d r lam k0))) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hfull hrem')

/-- The eventual threshold is uniform over all actual complete local unitary HS families. -/
theorem radialFirstHigh_bell_partialTranspose_eventually (d r : ℕ) (hd : 2≤d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
        (weightedBellMatrix (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialFirstHighWeights d r lam k0)))‖ ≤ 2*((n:ℝ)^12)⁻¹ := by
  obtain ⟨C,hC,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  filter_upwards [radialChoiTail_eventually_inverse d r hd lam 12,
    radialLowLabels_polynomial_ratio_inverse d r hd k0 C 0 1 12] with n hf hl
  intro W h0 hW hHS
  have h := radialFirstHigh_bell_partialTranspose_le d r n (by omega) lam W k0 h0 hW hHS hcard hC.le hmax
  have hl' : (radialLowLabels (S:=Fin n) d r k0).card*C/(d:ℝ)^n≤((n:ℝ)^12)⁻¹ := by
    simpa only [pow_zero,pow_one,mul_one,one_mul,mul_comm C] using hl
  exact h.trans (by linarith)

end CertificationGaussian
