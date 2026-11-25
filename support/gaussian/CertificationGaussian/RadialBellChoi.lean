import CertificationGaussian.BellTensorIdentity
import CertificationGaussian.RadialBellWeights

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {K S I : Type*} [Fintype K] [Fintype S] [Fintype I]
    [DecidableEq K] [DecidableEq S] [DecidableEq I]

omit [Fintype S] [DecidableEq S] [DecidableEq K] [DecidableEq I] in
theorem weightedBellMatrix_add_weight (W : K → Matrix I I ℂ) (a b : K → ℝ) :
    weightedBellMatrix W (fun k => a k+b k)=weightedBellMatrix W a+weightedBellMatrix W b := by
  simp only [weightedBellMatrix,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]

omit [Fintype S] [DecidableEq S] [DecidableEq K] [DecidableEq I] in
theorem weightedBellMatrix_smul_weight (W : K → Matrix I I ℂ) (c : ℝ) (a : K → ℝ) :
    weightedBellMatrix W (fun k => c*a k)=(c:ℂ) • weightedBellMatrix W a := by
  simp only [weightedBellMatrix,Complex.ofReal_mul,mul_smul,Finset.smul_sum]

omit [Fintype S] [DecidableEq S] [DecidableEq K] [DecidableEq I] in
theorem weightedBellMatrix_sum_weight {T : Type*} [Fintype T]
    (W : K → Matrix I I ℂ) (a : T → K → ℝ) :
    weightedBellMatrix W (fun k => ∑ t,a t k)=∑ t,weightedBellMatrix W (a t) := by
  simp only [weightedBellMatrix,Complex.ofReal_sum,Finset.sum_smul]
  exact Finset.sum_comm

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- The R0 spectral identity follows from actual HS completeness and the genuine identity label. -/
theorem radialBellRWeight_matrix (d : ℕ) (hd : 0<d) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) :
    weightedBellMatrix W (radialBellRWeight d k0)=radialChoiR0 d := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hs : (∑ k,unitaryBellProjector (W k))=1 :=
    unitaryBellProjector_sum_eq_one W (by simpa using hHS) (by simpa using hcard)
  have hw : radialBellRWeight d k0=(fun k => (d+1:ℝ)⁻¹-(if k=k0 then (d+1:ℝ)⁻¹ else 0)) := by
    funext k
    by_cases h : k=k0 <;> simp [radialBellRWeight,h]
  rw [hw,weightedBellMatrix_sub]
  have hc : weightedBellMatrix W (fun _ => (d+1:ℝ)⁻¹)=(Complex.ofReal ((d+1:ℝ)⁻¹)) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    change (∑ k,(Complex.ofReal ((d+1:ℝ)⁻¹)) • unitaryBellProjector (W k))=_
    rw [← Finset.smul_sum,hs]
  have hk : weightedBellMatrix W (fun k => if k=k0 then (d+1:ℝ)⁻¹ else 0)=
      (Complex.ofReal ((d+1:ℝ)⁻¹)) • unitaryBellProjector (W k0) := by
    simp only [weightedBellMatrix,unitaryBellProjector,apply_ite Complex.ofReal,
      Complex.ofReal_zero,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hc,hk,h0]
  simp only [radialChoiR0,radialChoiPhi,smul_sub,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- The A0 spectral identity uses the same original normalized identity Bell projector. -/
theorem radialBellAWeight_matrix (d : ℕ) (hd : 0<d) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) :
    weightedBellMatrix W (radialBellAWeight d k0)=radialChoiA0 d := by
  have hw : radialBellAWeight d k0=(fun k => (if k=k0 then 1 else 0)+radialBellRWeight d k0 k) := by
    funext k
    by_cases h : k=k0 <;> simp [radialBellAWeight,radialBellRWeight,h]
  rw [hw,weightedBellMatrix_add_weight,radialBellRWeight_matrix d hd W k0 h0 hHS hcard]
  have hk : weightedBellMatrix W (fun k => if k=k0 then 1 else 0)=unitaryBellProjector (W k0) := by
    simp [weightedBellMatrix,unitaryBellProjector,ite_smul]
  rw [hk,h0]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The genuine tensor Bell family realizes each fixed-subset local product. -/
theorem radialBell_tensor_matrix (d : ℕ) (hd : 0<d) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (J : Finset S) :
    weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
      (fun w => ∏ s,if s∈J then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s)) =
      radialChoiTensor d J := by
  rw [weightedBellMatrix_tensor W (fun s k =>
    if s∈J then radialBellRWeight d k0 k else radialBellAWeight d k0 k),radialChoiTensor]
  congr 1
  funext s
  by_cases hs : s∈J
  · simpa only [hs,ite_true] using radialBellRWeight_matrix d hd W k0 h0 hHS hcard
  · simpa only [hs,ite_false] using radialBellAWeight_matrix d hd W k0 h0 hHS hcard

omit [Fintype I] [DecidableEq I] in
/-- Exact identity between the actual weighted Bell matrix with the original radial coefficient and the explicit tensor Choi formula. -/
theorem radialFirstCoefficient_bell_matrix (d : ℕ) (hd : 0<d) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ) :
    weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
      (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card)=
      radialChoiCombination d r lam := by
  have hw : (fun w : S → K => radialFirstCoefficient d r lam (radialBellSupport k0 w).card)=
      (fun w => ∑ j : Fin (r+1),(d:ℝ)^j.val*lam j.val*
        ∑ J : {A : Finset S // A.card=j.val},
          ∏ s,if s∈J.val then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s)) := by
    funext w
    exact (radialBell_weight_formula d r lam k0 w).symm
  rw [hw,weightedBellMatrix_sum_weight]
  simp_rw [weightedBellMatrix_smul_weight,weightedBellMatrix_sum_weight,
    radialBell_tensor_matrix d hd W k0 h0 hHS hcard]
  simp only [radialChoiCombination,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]

omit [Fintype I] [DecidableEq I] in
/-- The second radial sequence is identified with the same actual squared-weight Choi operator. -/
theorem radialSecondCoefficient_bell_matrix (d : ℕ) (hd : 0<d) (W : K → Matrix (Fin d) (Fin d) ℂ)
    (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ) :
    weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
      (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card)=
      radialChoiSecondCombination d r lam := by
  simp only [radialSecondCoefficient,weightedBellMatrix_smul_weight,
    radialFirstCoefficient_bell_matrix d hd W k0 h0 hHS hcard,radialChoiSecondCombination,
    Complex.ofReal_ofNat]

omit [Fintype I] [DecidableEq I] in
/-- The true partially transposed weighted Bell operator has the original radial Choi-tail bound. -/
theorem radialFirstCoefficient_bell_partialTranspose_bound (d : ℕ) (hd : 0<d)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
      (weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card)))‖ ≤
      ∑ j : Fin (r+1),|lam j.val| * ((Fintype.card S).choose j.val:ℝ)*
        (2/(d+1:ℝ))^(Fintype.card S-j.val) := by
  rw [radialFirstCoefficient_bell_matrix d hd W k0 h0 hHS hcard,Matrix.l2_opNorm_toEuclideanCLM]
  exact radialChoiCombination_partialTranspose_norm_le d hd r lam

omit [Fintype I] [DecidableEq I] in
/-- The same true weighted Bell partial-transpose bound for the original second radial sequence. -/
theorem radialSecondCoefficient_bell_partialTranspose_bound (d : ℕ) (hd : 0<d)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
      (weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card)))‖ ≤
      2*∑ j : Fin (r+1),(lam j.val)^2 * ((Fintype.card S).choose j.val:ℝ)*
        (2/(d+1:ℝ))^(Fintype.card S-j.val) := by
  rw [radialSecondCoefficient_bell_matrix d hd W k0 h0 hHS hcard,Matrix.l2_opNorm_toEuclideanCLM]
  exact radialChoiSecondCombination_partialTranspose_norm_le d hd r lam

end CertificationGaussian
