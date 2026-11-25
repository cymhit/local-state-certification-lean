import CertificationGaussian.CardinalityComplementRemainder

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- The actual full-record rank-one effect is an idempotent projector. -/
theorem recordedProjector_mul_self (d : ℕ) (ω : ComplexUnitary (Fin d) × Fin d) :
    recordedProjector d ω*recordedProjector d ω=recordedProjector d ω := by
  let v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun i => ω.1.val i ω.2)
  have hv : vectorRankOne v v=recordedProjector d ω := rfl
  rw [← hv,vectorRankOne_mul,← vectorRankOne_trace,hv,recordedProjector_trace_one,one_smul]

/-- The two actual local factors P and I-P are orthogonal idempotents. -/
theorem localReadoutFactor_mul (d : ℕ) (a b : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    localReadoutFactor d a ω*localReadoutFactor d b ω=
      if a=b then localReadoutFactor d a ω else 0 := by
  have h := recordedProjector_mul_self d ω
  cases a <;> cases b <;>
    simp [localReadoutFactor,sub_mul,mul_sub,h]

section Sites
variable {S Ω : Type*} [Fintype S] [DecidableEq S]

/-- Distinct actual complement subsets give orthogonal tensor projectors. -/
theorem productReadoutFactor_mul (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (A B : Finset S) (ω : S → Ω) :
    productReadoutFactor d record A ω*productReadoutFactor d record B ω=
      if A=B then productReadoutFactor d record A ω else 0 := by
  rw [productReadoutFactor,productReadoutFactor,wickTensorMatrix_mul]
  by_cases hAB : A=B
  · subst B
    simp only [localReadoutFactor_mul,ite_true]
  · simp only [hAB,ite_false]
    have hn : ¬∀ s : S,s∈A ↔ s∈B := fun h => hAB (Finset.ext h)
    push Not at hn
    obtain ⟨s,hs⟩ := hn
    have hd : decide (s∈A)≠decide (s∈B) := by
      by_cases hA : s∈A <;> by_cases hB : s∈B <;> simp_all
    ext x y
    change (∏ t : S,(localReadoutFactor d (decide (t∈A)) (record (ω t))*
      localReadoutFactor d (decide (t∈B)) (record (ω t))) (x t) (y t))=0
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp only [localReadoutFactor_mul,hd,ite_false,Matrix.zero_apply])

/-- The exact trace counts one factor d-1 at each selected physical site. -/
theorem productReadoutFactor_trace (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : Finset S) (ω : S → Ω) :
    Matrix.trace (productReadoutFactor d record A ω)=((d:ℂ)-1)^A.card := by
  rw [productReadoutFactor,wickTensorMatrix_trace]
  simp only [localReadoutFactor_trace,decide_eq_true_eq]
  rw [Finset.prod_ite]
  simp

/-- The signed and squared coefficient trace scales of the actual cardinality kernel. -/
def cardinalityReadoutTraceScale (d n r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (r+1),lam j.val*(n.choose j.val:ℝ)*((d:ℝ)-1)^j.val

/-- Trace is independent of the basis/outcome record, with the original binomial multiplicities. -/
theorem cardinalityReadoutKernel_trace (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (r : ℕ) (lam : ℕ → ℝ) (ω : S → Ω) :
    Matrix.trace (cardinalityReadoutKernel d record r lam ω)=
      (cardinalityReadoutTraceScale d (Fintype.card S) r lam:ℂ) := by
  rw [cardinalityReadoutKernel_formula]
  simp only [Matrix.trace_sum,Matrix.trace_smul,productReadoutFactor_trace,
    cardinalityReadoutTraceScale,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_sub,Complex.ofReal_natCast,Complex.ofReal_one,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ J : {A : Finset S // A.card=j.val},((d:ℂ)-1)^J.val.card) =
      ((Fintype.card S).choose j.val:ℂ)*((d:ℂ)-1)^j.val := by
    have hc (J : {A : Finset S // A.card=j.val}) : J.val.card=j.val := J.property
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_finset_len]
  rw [he]
  ring

omit [Fintype S] [DecidableEq S] in
/-- The actual cardinality labels enumerate each subset at most once. -/
theorem cardinalityComplementSet_injective (r : ℕ) :
    Function.Injective (cardinalityComplementSet (S:=S) (r:=r)) := by
  rintro ⟨j,A⟩ ⟨k,B⟩ h
  change A.val=B.val at h
  have hj : j=k := Fin.ext (A.property.symm.trans ((congrArg Finset.card h).trans B.property))
  subst k
  have hAB : A=B := Subtype.ext h
  subst B
  rfl

/-- Squaring an actual signed sum of distinct complement projections squares its coefficients. -/
theorem finiteComplementKernel_sq {K : Type*} [Fintype K]
    (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : K → Finset S) (hA : Function.Injective A) (c : K → ℝ) (ω : S → Ω) :
    (finiteComplementKernel d record A c ω)^2 =
      finiteComplementKernel d record A (fun k => (c k)^2) ω := by
  classical
  simp only [pow_two,finiteComplementKernel,Finset.sum_mul,Finset.mul_sum,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,productReadoutFactor_mul,hA.eq_iff,
    smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Complex.ofReal_mul]

/-- The actual cardinality kernel square is the same kernel with the real coefficients squared. -/
theorem cardinalityReadoutKernel_sq (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (r : ℕ) (lam : ℕ → ℝ) (ω : S → Ω) :
    (cardinalityReadoutKernel d record r lam ω)^2 =
      cardinalityReadoutKernel d record r (fun j => (lam j)^2) ω :=
  finiteComplementKernel_sq d record _ (cardinalityComplementSet_injective r) _ ω

/-- The original nu_n is the true trace of H_s squared for every actual record. -/
theorem cardinalityReadoutKernel_trace_sq (d : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (r : ℕ) (lam : ℕ → ℝ) (ω : S → Ω) :
    Matrix.trace ((cardinalityReadoutKernel d record r lam ω)^2)=
      (cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2):ℂ) := by
  rw [cardinalityReadoutKernel_sq,cardinalityReadoutKernel_trace]

end Sites
end CertificationGaussian
