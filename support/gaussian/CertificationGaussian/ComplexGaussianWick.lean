import CertificationGaussian.ComplexGaussianWirtinger
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
open MeasureTheory MvPolynomial Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A mixed Gaussian monomial with separately indexed conjugate and unconjugated positions.
The coordinate maps may repeat values; positions, not labels, determine contraction multiplicity. -/
def gaussianMixedMonomial {A B : Type*} (s : Finset A) (t : Finset B) (i : A → I) (j : B → I) :
    MvPolynomial (Fin 2 × I) ℂ :=
  (∏ a ∈ s, gaussianBarZPolynomial (i a)) * (∏ b ∈ t, gaussianZPolynomial (j b))

omit [DecidableEq I] in
theorem gaussianMixedMonomial_actual_expectation {A B : Type*}
    (s : Finset A) (t : Finset B) (i : A → I) (j : B → I) :
    complexGaussianPolyExpectation (gaussianMixedMonomial s t i j) =
      ∫ x, (∏ a ∈ s, star (complexCoordinate x (i a))) * (∏ b ∈ t, complexCoordinate x (j b))
        ∂pairedGaussian I := by
  unfold complexGaussianPolyExpectation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [gaussianMixedMonomial, complexCoordinatePolyEval, map_mul, map_prod,
      show ∀ k, eval (fun c => (x c:ℂ)) (gaussianZPolynomial k) = complexCoordinate x k from
        fun k => complexCoordinatePolyEval_z k x,
      show ∀ k, eval (fun c => (x c:ℂ)) (gaussianBarZPolynomial k) = star (complexCoordinate x k) from
        fun k => complexCoordinatePolyEval_barz k x])

/-- Actual finite Wick recursion obtained from Gaussian IBP, without assuming any Wick identity. -/
theorem gaussianMixedMonomial_insert_bar {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (i : A → I) (j : B → I) (a : A) (ha : a ∉ s) :
    complexGaussianPolyExpectation (gaussianMixedMonomial (insert a s) t i j) =
      ∑ b ∈ t, if i a=j b then complexGaussianPolyExpectation (gaussianMixedMonomial s (t.erase b) i j) else 0 := by
  rw [gaussianMixedMonomial, Finset.prod_insert ha, mul_assoc, complexGaussianPolyExpectation_barz_ibp,
    wirtingerZ_mul]
  simp only [wirtingerZ_prod, wirtingerZ_barz, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum, complexGaussianPolyExpectation_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [wirtingerZ_z]
  by_cases h : i a=j b
  · simp [h, gaussianMixedMonomial]
  · simp [h, complexGaussianPolyExpectation_zero]

omit [DecidableEq I] in
theorem gaussianMixedMonomial_empty (A B : Type*) (i : A → I) (j : B → I) :
    complexGaussianPolyExpectation (gaussianMixedMonomial ∅ ∅ i j) = 1 := by
  simp only [gaussianMixedMonomial, Finset.prod_empty, mul_one]
  exact complexGaussianPolyExpectation_one


/-- Removing a position is exactly reindexing by succAbove; values may repeat. -/
theorem fin_prod_erase_succAbove {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n+1) → M) (b : Fin (n+1)) :
    (∏ k ∈ (Finset.univ : Finset (Fin (n+1))).erase b, f k) = ∏ k : Fin n, f (b.succAbove k) := by
  rw [Fin.univ_succAbove n b, Finset.erase_cons, Finset.prod_map]
  rfl

/-- Balanced monomials with separately labelled bar and unbar positions. -/
def gaussianBalancedMonomial (n : ℕ) (i j : Fin n → I) : MvPolynomial (Fin 2 × I) ℂ :=
  gaussianMixedMonomial Finset.univ Finset.univ i j

/-- The actual Gaussian moment satisfies the full sum over choices of a partner for the first bar position. -/
theorem gaussianBalancedMonomial_recursion (n : ℕ) (i j : Fin (n+1) → I) :
    complexGaussianPolyExpectation (gaussianBalancedMonomial (n+1) i j) =
      ∑ b : Fin (n+1), if i 0=j b then
        complexGaussianPolyExpectation (gaussianBalancedMonomial n
          (fun a => i a.succ) (fun a => j (b.succAbove a))) else 0 := by
  unfold gaussianBalancedMonomial gaussianMixedMonomial
  rw [Fin.prod_univ_succ (fun a => gaussianBarZPolynomial (i a)), mul_assoc,
    complexGaussianPolyExpectation_barz_ibp, wirtingerZ_mul]
  simp only [wirtingerZ_prod, wirtingerZ_barz, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum, complexGaussianPolyExpectation_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [wirtingerZ_z, fin_prod_erase_succAbove]
  by_cases h : i 0=j b
  · simp [h]
  · simp [h, complexGaussianPolyExpectation_zero]

/-- The permanent of the coordinate Kronecker-delta matrix, counting position permutations. -/
def complexGaussianPairingSum (n : ℕ) (i j : Fin n → I) : ℂ :=
  ∑ π : Equiv.Perm (Fin n), ∏ a, if i a=j (π a) then 1 else 0

omit [Fintype I] in
theorem complexGaussianPairingSum_recursion (n : ℕ) (i j : Fin (n+2) → I) :
    complexGaussianPairingSum (n+2) i j =
      ∑ b : Fin (n+2), if i 0=j b then
        complexGaussianPairingSum (n+1) (fun a => i a.succ) (fun a => j (b.succAbove a)) else 0 := by
  unfold complexGaussianPairingSum
  rw [← (Equiv.Perm.decomposeFin' (n := n)).symm.sum_comp
    (fun π : Equiv.Perm (Fin (n+2)) => ∏ a, if i a=j (π a) then (1:ℂ) else 0)]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin'Symm_zero, Equiv.Perm.decomposeFin'Symm_succ]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : i 0=j b <;> simp [h]
  rfl


/-- Full balanced complex Gaussian Wick identity in every order, counting all coordinate coincidences. -/
theorem complexGaussian_balanced_wick (n : ℕ) (i j : Fin n → I) :
    complexGaussianPolyExpectation (gaussianBalancedMonomial n i j) = complexGaussianPairingSum n i j := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [gaussianBalancedMonomial, gaussianMixedMonomial, complexGaussianPairingSum,
      complexGaussianPolyExpectation_one]
  | one =>
    rw [gaussianBalancedMonomial_recursion, Fin.sum_univ_one]
    have he (a b : Fin 0 → I) : complexGaussianPolyExpectation (gaussianBalancedMonomial 0 a b) = 1 := by
      simp [gaussianBalancedMonomial, gaussianMixedMonomial, complexGaussianPolyExpectation_one]
    simp_rw [he]
    unfold complexGaussianPairingSum
    rw [Finset.sum_eq_single (Equiv.refl (Fin 1))]
    · rw [Fin.prod_univ_one]
      rfl
    · intro π _ hπ
      exact (hπ (Subsingleton.elim _ _)).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  | more n _ ih =>
    rw [gaussianBalancedMonomial_recursion, complexGaussianPairingSum_recursion]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : i 0=j b <;> simp [h, ih]

/-- Explicit integral form under the true normalized complex Gaussian law. -/
theorem complexGaussian_balanced_wick_integral (n : ℕ) (i j : Fin n → I) :
    (∫ x, (∏ a, star (complexCoordinate x (i a))) * (∏ b, complexCoordinate x (j b))
      ∂pairedGaussian I) =
        ∑ π : Equiv.Perm (Fin n), ∏ a, if i a=j (π a) then (1:ℂ) else 0 := by
  rw [← gaussianMixedMonomial_actual_expectation]
  exact complexGaussian_balanced_wick n i j

/-- Repeated coordinate labels count all n! pairings, rather than just distinct labels. -/
theorem complexGaussian_same_coordinate_moment (n : ℕ) (i : I) :
    (∫ x, star (complexCoordinate x i)^n * complexCoordinate x i^n ∂pairedGaussian I) =
      (n.factorial : ℂ) := by
  simpa [Fintype.card_perm] using
    complexGaussian_balanced_wick_integral n (fun _ => i) (fun _ => i)

/-- The two-point contraction, including coincident coordinates. -/
theorem gaussianBalancedMonomial_one (i j : Fin 1 → I) :
    complexGaussianPolyExpectation (gaussianBalancedMonomial 1 i j) =
      if i 0=j 0 then 1 else 0 := by
  rw [gaussianBalancedMonomial_recursion, Fin.sum_univ_one]
  have he (a b : Fin 0 → I) : complexGaussianPolyExpectation (gaussianBalancedMonomial 0 a b)=1 := by
    simp [gaussianBalancedMonomial, gaussianMixedMonomial, complexGaussianPolyExpectation_one]
  simp_rw [he]

/-- The fourth moment has two pairings, with no distinctness assumption on the labels. -/
theorem gaussianBalancedMonomial_two (i j : Fin 2 → I) :
    complexGaussianPolyExpectation (gaussianBalancedMonomial 2 i j) =
      (if i 0=j 0 then (1:ℂ) else 0)*(if i 1=j 1 then 1 else 0) +
      (if i 0=j 1 then (1:ℂ) else 0)*(if i 1=j 0 then 1 else 0) := by
  rw [gaussianBalancedMonomial_recursion, Fin.sum_univ_two]
  simp_rw [gaussianBalancedMonomial_one]
  norm_num [Fin.succAbove]
  split_ifs <;> ring

/-- Explicit two-pairing formula under the same normalized complex Gaussian law. -/
theorem complexGaussian_fourth_moment (i j : Fin 2 → I) :
    (∫ x, (star (complexCoordinate x (i 0))*star (complexCoordinate x (i 1))) *
      (complexCoordinate x (j 0)*complexCoordinate x (j 1)) ∂pairedGaussian I) =
      (if i 0=j 0 then (1:ℂ) else 0)*(if i 1=j 1 then 1 else 0) +
      (if i 0=j 1 then (1:ℂ) else 0)*(if i 1=j 0 then 1 else 0) := by
  have h := gaussianBalancedMonomial_two i j
  rw [gaussianBalancedMonomial, gaussianMixedMonomial_actual_expectation] at h
  simpa only [Fin.prod_univ_two] using h

end CertificationGaussian
