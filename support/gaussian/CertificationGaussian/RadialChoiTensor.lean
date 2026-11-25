import CertificationGaussian.RadialChoiLocal
import CertificationGaussian.TensorOperatorNorm
import Mathlib.Data.Fintype.Powerset

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

/-- The actual tensor on the global input/output pair, in the Bell first-factor ordering. -/
def pairedTensorMatrix (A : S → Matrix (I × I) (I × I) ℂ) :
    Matrix ((S → I) × (S → I)) ((S → I) × (S → I)) ℂ :=
  fun p q => ∏ s,A s (p.1 s,p.2 s) (q.1 s,q.2 s)

omit [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- A genuine coordinate equivalence, not a replacement of the global matrix by a new norm. -/
theorem pairedTensorMatrix_eq_submatrix (A : S → Matrix (I × I) (I × I) ℂ) :
    pairedTensorMatrix A=(wickTensorMatrix A).submatrix
      (Equiv.arrowProdEquivProdArrow S (fun _ => I) (fun _ => I)).symm
      (Equiv.arrowProdEquivProdArrow S (fun _ => I) (fun _ => I)).symm := rfl

omit [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- The same global first partial transpose acts at every physical site. -/
theorem pairedTensorMatrix_partialTranspose (A : S → Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (pairedTensorMatrix A)=
      pairedTensorMatrix (fun s => partialTransposeFirst (A s)) := rfl

/-- True L2 operator norm of the matrix on the global pair. -/
theorem pairedTensorMatrix_norm (A : S → Matrix (I × I) (I × I) ℂ) :
    ‖pairedTensorMatrix A‖=∏ s,‖A s‖ := by
  rw [pairedTensorMatrix_eq_submatrix,matrix_l2_opNorm_submatrix_equiv,wickTensorMatrix_norm]

/-- The actual product of R0 on J and A0 off J, on the original global pair index. -/
def radialChoiTensor (d : ℕ) (J : Finset S) :
    Matrix ((S → Fin d) × (S → Fin d)) ((S → Fin d) × (S → Fin d)) ℂ :=
  pairedTensorMatrix (fun s => if s∈J then radialChoiR0 d else radialChoiA0 d)

/-- The precise per-subset tensor estimate, before the d^j cancellation. -/
theorem radialChoiTensor_partialTranspose_norm_le (d : ℕ) (hd : 0<d) (J : Finset S) :
    ‖partialTransposeFirst (radialChoiTensor d J)‖ ≤
      (d:ℝ)⁻¹^J.card * (2/(d+1:ℝ))^(Fintype.card S-J.card) := by
  rw [radialChoiTensor,pairedTensorMatrix_partialTranspose,pairedTensorMatrix_norm]
  calc
    _ ≤ ∏ s : S,if s∈J then (d:ℝ)⁻¹ else 2/(d+1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro s _
      by_cases hs : s∈J
      · simpa [hs] using radialChoiR0_partialTranspose_norm_le d hd
      · simpa [hs] using radialChoiA0_partialTranspose_norm_le d hd
    _ = _ := by
      rw [Finset.prod_ite]
      simp [Finset.filter_not,Finset.card_sdiff,div_pow]

/-- The original finite tensor formula for the first radial Choi matrix, with arbitrary signed coefficients. -/
def radialChoiCombination (d r : ℕ) (lam : ℕ → ℝ) :
    Matrix ((S → Fin d) × (S → Fin d)) ((S → Fin d) × (S → Fin d)) ℂ :=
  ∑ j : Fin (r+1),((d:ℂ)^j.val*(lam j.val:ℂ)) •
    ∑ J : {A : Finset S // A.card=j.val},radialChoiTensor d J.val

/-- The original second radial Choi tensor formula. -/
def radialChoiSecondCombination (d r : ℕ) (lam : ℕ → ℝ) :
    Matrix ((S → Fin d) × (S → Fin d)) ((S → Fin d) × (S → Fin d)) ℂ :=
  (2:ℂ) • radialChoiCombination d r (fun j => (lam j)^2)

/-- The paper's Choi-tail bound for the actual finite tensor sum; j>n fibers are empty. -/
theorem radialChoiCombination_partialTranspose_norm_le (d : ℕ) (hd : 0<d)
    (r : ℕ) (lam : ℕ → ℝ) :
    ‖partialTransposeFirst (radialChoiCombination (S:=S) d r lam)‖ ≤
      ∑ j : Fin (r+1),|lam j.val| *((Fintype.card S).choose j.val:ℝ)*
        (2/(d+1:ℝ))^(Fintype.card S-j.val) := by
  have hd0 : (d:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [radialChoiCombination,partialTransposeFirst_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [partialTransposeFirst_smul,norm_smul,norm_mul,norm_pow,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,partialTransposeFirst_sum]
  calc
    _ ≤ ((d:ℝ)^j.val*|lam j.val|) *
        ∑ J : {A : Finset S // A.card=j.val},‖partialTransposeFirst (radialChoiTensor d J.val)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((d:ℝ)^j.val*|lam j.val|) *
        ∑ _J : {A : Finset S // A.card=j.val},
          (d:ℝ)⁻¹^j.val*(2/(d+1:ℝ))^(Fintype.card S-j.val) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun J _ => by simpa [J.property] using
        radialChoiTensor_partialTranspose_norm_le d hd J.val)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_finset_len]
      rw [inv_pow]
      field_simp

/-- The squared-weight companion has the exact factor two of the original formula. -/
theorem radialChoiSecondCombination_partialTranspose_norm_le (d : ℕ) (hd : 0<d)
    (r : ℕ) (lam : ℕ → ℝ) :
    ‖partialTransposeFirst (radialChoiSecondCombination (S:=S) d r lam)‖ ≤
      2*∑ j : Fin (r+1),(lam j.val)^2*((Fintype.card S).choose j.val:ℝ)*
        (2/(d+1:ℝ))^(Fintype.card S-j.val) := by
  rw [radialChoiSecondCombination,partialTransposeFirst_smul,norm_smul]
  have h := radialChoiCombination_partialTranspose_norm_le (S:=S) d hd r (fun j => (lam j)^2)
  simpa only [Complex.norm_ofNat,abs_sq] using
    mul_le_mul_of_nonneg_left h (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
