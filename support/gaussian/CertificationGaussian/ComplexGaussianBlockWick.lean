import CertificationGaussian.ComplexGaussianNormalOrder

noncomputable section
open MeasureTheory MvPolynomial Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I B : Type*} [DecidableEq I] [DecidableEq B]

/-- Polynomial partial derivatives commute, proved on the actual polynomial ring. -/
theorem gaussian_pderiv_commute (i j : Fin 2 × I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P k hP =>
    by_cases hi : k=i <;> by_cases hj : k=j <;> by_cases hij : i=j <;>
      simp [pderiv_X, hi, hj, hij, eq_comm, hP] <;> ring

/-- Only same-kind Wirtinger commutation is required by the finite block recurrence. -/
theorem wirtingerZ_commute (i j : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerZ i (wirtingerZ j P) = wirtingerZ j (wirtingerZ i P) := by
  simp only [wirtingerZ, pderiv_mul, pderiv_C, zero_mul, zero_add, map_sub]
  rw [gaussian_pderiv_commute (0,i) (0,j), gaussian_pderiv_commute (0,i) (1,j),
    gaussian_pderiv_commute (1,i) (0,j), gaussian_pderiv_commute (1,i) (1,j)]
  ring

omit [DecidableEq I] in
theorem gaussianBarCreation_add (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    gaussianBarCreation i (P+Q) = gaussianBarCreation i P + gaussianBarCreation i Q := by
  simp only [gaussianBarCreation, mul_add, wirtingerZ_add]
  ring

omit [DecidableEq I] in
theorem gaussianBarCreation_zero (i : I) :
    gaussianBarCreation i (0 : MvPolynomial (Fin 2 × I) ℂ) = 0 := by
  simp [gaussianBarCreation,wirtingerZ]

omit [DecidableEq I] in
theorem gaussianBarCreation_C_mul (i : I) (c : ℂ) (P : MvPolynomial (Fin 2 × I) ℂ) :
    gaussianBarCreation i (C c*P) = C c*gaussianBarCreation i P := by
  simp only [gaussianBarCreation, wirtingerZ_mul, wirtingerZ_C, zero_mul, zero_add]
  ring

omit [DecidableEq I] in
theorem gaussianBarCreation_sum {J : Type*} (s : Finset J)
    (f : J → MvPolynomial (Fin 2 × I) ℂ) (i : I) :
    gaussianBarCreation i (∑ j ∈ s, f j) = ∑ j ∈ s, gaussianBarCreation i (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussianBarCreation_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, gaussianBarCreation_add, ih]

/-- A z-derivative commutes with conjugate creation: there is no hidden self-contraction. -/
theorem wirtingerZ_gaussianBarCreation (i j : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerZ i (gaussianBarCreation j P) = gaussianBarCreation j (wirtingerZ i P) := by
  simp only [gaussianBarCreation, wirtingerZ_sub, wirtingerZ_mul, wirtingerZ_barz,
    zero_mul, zero_add, wirtingerZ_commute i j]

/-- One block with independently sized bar and unbar lists of global positions.
The recursion preserves positions even when coordinate labels repeat. -/
def gaussianNormalBlock : (m n : ℕ) → (Fin m → B) → (Fin n → B) →
    (Fin m → I) → (Fin n → I) → B → MvPolynomial (Fin 2 × I) ℂ
  | 0, n, _, e, _, j, b => ∏ t : Fin n, if e t=b then gaussianZPolynomial (j t) else 1
  | m+1, n, c, e, i, j, b =>
    if c 0=b then gaussianBarCreation (i 0)
      (gaussianNormalBlock m n (fun a => c a.succ) e (fun a => i a.succ) j b)
    else gaussianNormalBlock m n (fun a => c a.succ) e (fun a => i a.succ) j b

omit [DecidableEq I] in
/-- Deleting a z-position belonging to another block changes no polynomial in this block. -/
theorem gaussianNormalBlock_delete_other (m n : ℕ) (c : Fin m → B) (e : Fin (n+1) → B)
    (i : Fin m → I) (j : Fin (n+1) → I) (b : B) (t : Fin (n+1)) (ht : e t ≠ b) :
    gaussianNormalBlock m (n+1) c e i j b =
      gaussianNormalBlock m n c (fun a => e (t.succAbove a)) i (fun a => j (t.succAbove a)) b := by
  induction m with
  | zero =>
    simp only [gaussianNormalBlock]
    rw [Fin.prod_univ_succAbove _ t]
    simp [ht]
  | succ m ih =>
    simp only [gaussianNormalBlock]
    rw [ih]

/-- The derivative removes one unbar position of this block, summing by positions rather than values. -/
theorem wirtingerZ_gaussianNormalBlock (m n : ℕ) (c : Fin m → B) (e : Fin (n+1) → B)
    (i : Fin m → I) (j : Fin (n+1) → I) (b : B) (k : I) :
    wirtingerZ k (gaussianNormalBlock m (n+1) c e i j b) =
      ∑ t : Fin (n+1), if e t=b ∧ k=j t then
        gaussianNormalBlock m n c (fun a => e (t.succAbove a)) i (fun a => j (t.succAbove a)) b
      else 0 := by
  induction m with
  | zero =>
    simp only [gaussianNormalBlock, wirtingerZ_prod]
    apply Finset.sum_congr rfl
    intro t _
    rw [fin_prod_erase_succAbove]
    have hz1 (a : I) : wirtingerZ a (1 : MvPolynomial (Fin 2 × I) ℂ)=0 := by
      simpa only [map_one] using wirtingerZ_C a 1
    by_cases ht : e t=b <;> by_cases hk : k=j t <;>
      simp [ht,hk,wirtingerZ_z,hz1]
  | succ m ih =>
    simp only [gaussianNormalBlock]
    by_cases hc : c 0=b
    · simp only [hc, ite_true, wirtingerZ_gaussianBarCreation, ih, gaussianBarCreation_sum]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : e t=b ∧ k=j t <;> simp [h,gaussianBarCreation_zero]
    · simp only [hc, ite_false, ih]

/-- The product of normal polynomials over all blocks; individual blocks may be unbalanced. -/
def gaussianNormalProduct [Fintype B] (m n : ℕ) (c : Fin m → B) (e : Fin n → B)
    (i : Fin m → I) (j : Fin n → I) : MvPolynomial (Fin 2 × I) ℂ :=
  ∏ b, gaussianNormalBlock m n c e i j b

omit [DecidableEq I] in
theorem gaussianNormalProduct_succ_bar [Fintype B] (m n : ℕ)
    (c : Fin (m+1) → B) (e : Fin n → B) (i : Fin (m+1) → I) (j : Fin n → I) :
    gaussianNormalProduct (m+1) n c e i j =
      gaussianBarCreation (i 0) (gaussianNormalBlock m n (fun a => c a.succ) e (fun a => i a.succ) j (c 0)) *
        ∏ b ∈ (Finset.univ : Finset B).erase (c 0),
          gaussianNormalBlock m n (fun a => c a.succ) e (fun a => i a.succ) j b := by
  unfold gaussianNormalProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (c 0))]
  simp only [gaussianNormalBlock, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  simp [Ne.symm (Finset.mem_erase.mp hb).1]

omit [DecidableEq I] in
/-- Recombining a lowered block with all other blocks is exactly deleting that global position. -/
theorem gaussianNormalProduct_delete_term [Fintype B] (m n : ℕ)
    (c : Fin m → B) (e : Fin (n+1) → B) (i : Fin m → I) (j : Fin (n+1) → I)
    (q : B) (t : Fin (n+1)) (hqt : q ≠ e t) :
    gaussianNormalBlock m (n+1) c e i j q *
      (gaussianNormalBlock m n c (fun a => e (t.succAbove a)) i (fun a => j (t.succAbove a)) (e t) *
        ∏ b ∈ ((Finset.univ : Finset B).erase q).erase (e t), gaussianNormalBlock m (n+1) c e i j b) =
      gaussianNormalProduct m n c (fun a => e (t.succAbove a)) i (fun a => j (t.succAbove a)) := by
  unfold gaussianNormalProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hqt,Finset.mem_univ _⟩)]
  rw [gaussianNormalBlock_delete_other m n c e i j q t (Ne.symm hqt)]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact gaussianNormalBlock_delete_other m n c e i j b t (Ne.symm (Finset.mem_erase.mp hb).1)

/-- True Gaussian expectation has only between-block contractions.
The deleted position is global, so repeated labels keep their full multiplicity. -/
theorem gaussianNormalProduct_recursion [Fintype I] [Fintype B] (m n : ℕ)
    (c : Fin (m+1) → B) (e : Fin (n+1) → B) (i : Fin (m+1) → I) (j : Fin (n+1) → I) :
    complexGaussianPolyExpectation (gaussianNormalProduct (m+1) (n+1) c e i j) =
      ∑ t : Fin (n+1), if c 0 ≠ e t ∧ i 0=j t then
        complexGaussianPolyExpectation (gaussianNormalProduct m n
          (fun a => c a.succ) (fun a => e (t.succAbove a))
          (fun a => i a.succ) (fun a => j (t.succAbove a))) else 0 := by
  rw [gaussianNormalProduct_succ_bar, gaussianBarCreation_adjoint, wirtingerZ_prod]
  simp_rw [wirtingerZ_gaussianNormalBlock]
  simp only [Finset.sum_mul, Finset.mul_sum, complexGaussianPolyExpectation_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hi : i 0=j t
  · by_cases hc : c 0=e t
    · rw [ite_eq_right (by simp [hc])]
      apply Finset.sum_eq_zero
      intro b hb
      have he : e t ≠ b := by
        rw [← hc]
        exact Ne.symm (Finset.mem_erase.mp hb).1
      simp [he,complexGaussianPolyExpectation_zero]
    · rw [ite_eq_left ⟨hc,hi⟩]
      rw [Finset.sum_eq_single (e t)]
      · simp only [hi, and_self, ite_true]
        rw [gaussianNormalProduct_delete_term m n _ _ _ _ (c 0) t hc]
      · intro b _ hb
        simp [Ne.symm hb,complexGaussianPolyExpectation_zero]
      · intro h
        exact (h (Finset.mem_erase.mpr ⟨Ne.symm hc,Finset.mem_univ _⟩)).elim
  · simp [hi,complexGaussianPolyExpectation_zero]

/-- A weighted sum over position permutations with every within-block edge forbidden. -/
def complexGaussianBlockPairingSum (n : ℕ) (c e : Fin n → B) (i j : Fin n → I) : ℂ :=
  ∑ π : Equiv.Perm (Fin n), ∏ a, if c a ≠ e (π a) ∧ i a=j (π a) then 1 else 0

theorem complexGaussianBlockPairingSum_recursion (n : ℕ)
    (c e : Fin (n+2) → B) (i j : Fin (n+2) → I) :
    complexGaussianBlockPairingSum (n+2) c e i j =
      ∑ t : Fin (n+2), if c 0 ≠ e t ∧ i 0=j t then
        complexGaussianBlockPairingSum (n+1) (fun a => c a.succ) (fun a => e (t.succAbove a))
          (fun a => i a.succ) (fun a => j (t.succAbove a)) else 0 := by
  unfold complexGaussianBlockPairingSum
  rw [← (Equiv.Perm.decomposeFin' (n := n)).symm.sum_comp
    (fun π : Equiv.Perm (Fin (n+2)) =>
      ∏ a, if c a ≠ e (π a) ∧ i a=j (π a) then (1:ℂ) else 0)]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin'Symm_zero, Equiv.Perm.decomposeFin'Symm_succ]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : c 0 ≠ e t ∧ i 0=j t <;> simp [h]
  rfl

/-- The full finite normal-order Wick identity in every order and for every finite block set.
Individual blocks need not be balanced, and repeated labels retain position multiplicity. -/
theorem complexGaussian_block_wick [Fintype I] [Fintype B] (n : ℕ)
    (c e : Fin n → B) (i j : Fin n → I) :
    complexGaussianPolyExpectation (gaussianNormalProduct n n c e i j) =
      complexGaussianBlockPairingSum n c e i j := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [gaussianNormalProduct,gaussianNormalBlock,complexGaussianBlockPairingSum,
      complexGaussianPolyExpectation_one]
  | one =>
    rw [gaussianNormalProduct_recursion,Fin.sum_univ_one]
    have he (a b : Fin 0 → I) (cc ee : Fin 0 → B) :
        complexGaussianPolyExpectation (gaussianNormalProduct 0 0 cc ee a b)=1 := by
      simp [gaussianNormalProduct,gaussianNormalBlock,complexGaussianPolyExpectation_one]
    simp_rw [he]
    unfold complexGaussianBlockPairingSum
    rw [Finset.sum_eq_single (Equiv.refl (Fin 1))]
    · rw [Fin.prod_univ_one]
      rfl
    · intro π _ hπ
      exact (hπ (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  | more n _ ih =>
    rw [gaussianNormalProduct_recursion,complexGaussianBlockPairingSum_recursion]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : c 0 ≠ e t ∧ i 0=j t <;> simp [h,ih]

/-- Explicit actual integral form of the complete finite block-exclusion identity. -/
theorem complexGaussian_block_wick_integral [Fintype I] [Fintype B] (n : ℕ)
    (c e : Fin n → B) (i j : Fin n → I) :
    (∫ x, ∏ b, complexCoordinatePolyEval (gaussianNormalBlock n n c e i j b) x ∂pairedGaussian I) =
      ∑ π : Equiv.Perm (Fin n), ∏ a, if c a ≠ e (π a) ∧ i a=j (π a) then (1:ℂ) else 0 := by
  have h := complexGaussian_block_wick n c e i j
  simpa only [complexGaussianPolyExpectation,gaussianNormalProduct,complexCoordinatePolyEval,map_prod,
    complexGaussianBlockPairingSum] using h

end CertificationGaussian
