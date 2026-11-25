import GaussianHilbert.WienerChaos

/- Ordinary finite-dimensional polynomial total degree implies Hermite/chaosLE membership.
No hypercontractive bound is imported or assumed in this layer. -/
noncomputable section
open MeasureTheory GaussianHilbert
open scoped BigOperators
namespace CertificationGaussian

def hermiteSpanLE (m k : Nat) : Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ α : Fin m → Nat, (∑ i, α i) ≤ k ∧ f = hermiteMultiEval α}

theorem hermiteSpanLE_mono {m a b : Nat} (h : a ≤ b) : hermiteSpanLE m a ≤ hermiteSpanLE m b := by
  apply Submodule.span_mono
  rintro f ⟨α, hα, rfl⟩
  exact ⟨α, hα.trans h, rfl⟩

theorem hermite_mem_span {m k : Nat} (α : Fin m → Nat) (h : (∑ i, α i) ≤ k) :
    hermiteMultiEval α ∈ hermiteSpanLE m k := Submodule.subset_span ⟨α, h, rfl⟩

theorem coord_mul_span {m k : Nat} (j : Fin m) {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ hermiteSpanLE m k) : (fun x => x j * f x) ∈ hermiteSpanLE m (k+1) := by
  classical
  let M : ((Fin m → ℝ) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) → ℝ) :=
    { toFun := fun g x => x j * g x
      map_add' := by intros; ext x; simp [mul_add]
      map_smul' := by intros; ext x; simp [mul_left_comm] }
  have hmap : Submodule.map M (hermiteSpanLE m k) ≤ hermiteSpanLE m (k+1) := by
    rw [hermiteSpanLE, Submodule.map_span_le]
    rintro g ⟨α, hα, rfl⟩
    have hup : (∑ i, Function.update α j (α j+1) i) ≤ k+1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
      have hs := Finset.sum_erase_add Finset.univ α (Finset.mem_univ j)
      simp only [Finset.sdiff_singleton_eq_erase] at *
      omega
    have hdown : (∑ i, Function.update α j (α j-1) i) ≤ k+1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
      have hs := Finset.sum_erase_add Finset.univ α (Finset.mem_univ j)
      simp only [Finset.sdiff_singleton_eq_erase] at *
      omega
    have heq : M (hermiteMultiEval α) = hermiteMultiEval (Function.update α j (α j+1)) +
        (α j : ℝ) • hermiteMultiEval (Function.update α j (α j-1)) := by
      ext x
      exact x_mul_hermiteMultiEval j α x
    rw [heq]
    exact (hermiteSpanLE m (k+1)).add_mem (hermite_mem_span _ hup)
      ((hermiteSpanLE m (k+1)).smul_mem _ (hermite_mem_span _ hdown))
  exact hmap ⟨f, hf, rfl⟩

theorem monomial_span {m : Nat} (α : Fin m → Nat) :
    (fun x : Fin m → ℝ => ∏ i, x i ^ α i) ∈ hermiteSpanLE m (∑ i, α i) := by
  classical
  generalize hk : (∑ i, α i) = k
  induction k using Nat.strong_induction_on generalizing α with
  | h k ih =>
    by_cases hzero : α = 0
    · subst α
      have heq : (fun x : Fin m → ℝ => ∏ i, x i ^ (0 : Fin m → Nat) i) =
          hermiteMultiEval (0 : Fin m → Nat) := by
        ext x
        simp [hermiteMultiEval, hermiteEval_zero]
      rw [heq]
      exact hermite_mem_span _ (by simp)
    · obtain ⟨j, hj⟩ : ∃ j, 0 < α j := by
        by_contra! hn
        apply hzero
        ext i
        exact Nat.eq_zero_of_le_zero (hn i)
      let β := Function.update α j (α j-1)
      have hb : (∑ i, β i) + 1 = k := by
        dsimp [β]
        rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
        have hs := Finset.sum_erase_add Finset.univ α (Finset.mem_univ j)
        simp only [Finset.sdiff_singleton_eq_erase] at *
        omega
      have hm := coord_mul_span j (ih (∑ i, β i) (by omega) β rfl)
      have heq : (fun x : Fin m → ℝ => x j * ∏ i, x i ^ β i) =
          (fun x => ∏ i, x i ^ α i) := by
        ext x
        have hp : (fun i => x i ^ β i) = Function.update (fun i => x i ^ α i) j (x j ^ (α j-1)) := by
          ext i
          by_cases hi : i = j
          · subst i; simp [β]
          · simp [β, Function.update_of_ne hi]
        rw [hp, Finset.prod_update_of_mem (Finset.mem_univ j)]
        simp only [Finset.sdiff_singleton_eq_erase]
        rw [← mul_assoc, ← pow_succ']
        have hj' : α j-1+1 = α j := by omega
        rw [hj']
        exact Finset.mul_prod_erase Finset.univ (fun i => x i ^ α i) (Finset.mem_univ j)
      rw [heq, hb] at hm
      exact hm

theorem eval_span {m : Nat} (P : MvPolynomial (Fin m) ℝ) :
    (fun x => MvPolynomial.eval x P) ∈ hermiteSpanLE m P.totalDegree := by
  classical
  have heq : (fun x => MvPolynomial.eval x P) =
      ∑ α ∈ P.support, P.coeff α • (fun x : Fin m → ℝ => ∏ i, x i ^ α i) := by
    ext x
    simpa using MvPolynomial.eval_eq' x P
  rw [heq]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  apply hermiteSpanLE_mono (b := P.totalDegree) _ (monomial_span α)
  have h := MvPolynomial.le_totalDegree hα
  rw [Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)] at h
  exact h

theorem span_lift {m k : Nat} {f : (Fin m → ℝ) → ℝ} (hf : f ∈ hermiteSpanLE m k) :
    ∃ F : Lp ℝ 2 (stdGaussianFin m), F ∈ wienerChaosLE m k ∧ (F : (Fin m → ℝ) → ℝ) =ᵐ[stdGaussianFin m] f := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, hα, rfl⟩ := hf
    refine ⟨hermiteMultiLp α, ?_, hermiteMultiLp_coeFn α⟩
    have hle : wienerChaos m (∑ i, α i) ≤ wienerChaosLE m k := by
      unfold wienerChaosLE
      exact le_iSup_of_le (∑ i, α i) (le_iSup_of_le (Finset.mem_range.mpr (by omega)) le_rfl)
    exact hle (hermiteMultiLp_mem_wienerChaos m α)
  | zero => exact ⟨0, Submodule.zero_mem _, Lp.coeFn_zero _ _ _⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨F, hF, hFe⟩ := ihf
    obtain ⟨G, hG, hGe⟩ := ihg
    exact ⟨F+G, Submodule.add_mem _ hF hG, (Lp.coeFn_add F G).trans (hFe.add hGe)⟩
  | smul c f hf ih =>
    obtain ⟨F, hF, hFe⟩ := ih
    exact ⟨c • F, Submodule.smul_mem _ c hF, (Lp.coeFn_smul c F).trans (hFe.const_smul c)⟩

theorem eval_memLp_two {m : Nat} (P : MvPolynomial (Fin m) ℝ) :
    MemLp (fun x => MvPolynomial.eval x P) 2 (stdGaussianFin m) := by
  let : IsProbabilityMeasure (stdGaussianFin m) := by unfold stdGaussianFin; infer_instance
  exact MvPolynomial_eval_memLp_two_of_subGaussian _ (isSubGaussianMeasure_pi_gaussianReal m) P

def polynomialLp {m : Nat} (P : MvPolynomial (Fin m) ℝ) : Lp ℝ 2 (stdGaussianFin m) :=
  (eval_memLp_two P).toLp _

theorem polynomialLp_ae {m : Nat} (P : MvPolynomial (Fin m) ℝ) :
    (polynomialLp P : (Fin m → ℝ) → ℝ) =ᵐ[stdGaussianFin m] (fun x => MvPolynomial.eval x P) :=
  MemLp.coeFn_toLp _

theorem polynomialLp_mem_chaosLE {m k : Nat} (P : MvPolynomial (Fin m) ℝ) (hP : P.totalDegree ≤ k) :
    polynomialLp P ∈ wienerChaosLE m k := by
  obtain ⟨F, hF, hFe⟩ := span_lift (hermiteSpanLE_mono hP (eval_span P))
  have heq : polynomialLp P = F := Lp.ext ((polynomialLp_ae P).trans hFe.symm)
  exact heq ▸ hF

theorem polynomial_eval_measurable {m : Nat} (P : MvPolynomial (Fin m) ℝ) :
    Measurable (fun x => MvPolynomial.eval x P) := P.continuous_eval.measurable

theorem zero_polynomial_chaos (m : Nat) :
    polynomialLp (0 : MvPolynomial (Fin m) ℝ) ∈ wienerChaosLE m 4 :=
  polynomialLp_mem_chaosLE _ (by simp)

theorem constant_polynomial_chaos (m : Nat) (c : ℝ) :
    polynomialLp (MvPolynomial.C c : MvPolynomial (Fin m) ℝ) ∈ wienerChaosLE m 4 :=
  polynomialLp_mem_chaosLE _ (by simp)

theorem empty_coordinates_eval (P : MvPolynomial (Fin 0) ℝ) (x : Fin 0 → ℝ) :
    MvPolynomial.eval x P = P.coeff 0 := by
  rw [MvPolynomial.eq_C_of_isEmpty P]
  simp

end CertificationGaussian
