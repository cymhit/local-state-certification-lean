import CertificationGaussian.RadialChoiTensor

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K S : Type*} [Fintype I] [Fintype K] [Fintype S]
    [DecidableEq I] [DecidableEq K] [DecidableEq S]

omit [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S] [DecidableEq I] in
/-- The same normalized Bell projector, with the square-root normalization multiplied out. -/
theorem unitaryBellProjector_apply (U : Matrix I I ℂ) (p q : I × I) :
    unitaryBellProjector U p q=U p.2 p.1*star (U q.2 q.1)/(Fintype.card I:ℂ) := by
  have hs : (Real.sqrt (Fintype.card I:ℝ):ℂ)^2=(Fintype.card I:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))
  simp only [unitaryBellProjector,unitaryBellVector,Matrix.vecMulVec_apply,
    star_div₀,Complex.star_def,Complex.conj_ofReal]
  rw [div_mul_div_comm,← pow_two,hs]

omit [Fintype S] [DecidableEq S] in
/-- A full Hilbert-Schmidt orthogonal family resolves the actual identity Bell space. -/
theorem unitaryBellProjector_sum_eq_one [Nonempty I] (W : K → Matrix I I ℂ)
    (hHS : ∀ w v,Matrix.trace ((W w)ᴴ*W v)=if w=v then (Fintype.card I:ℂ) else 0)
    (hcard : Fintype.card K=(Fintype.card I)^2) :
    (∑ w,unitaryBellProjector (W w))=1 := by
  have hv := unitaryBellVector_orthonormal W hHS
  have hc : Fintype.card K=Module.finrank ℂ (EuclideanSpace ℂ (I × I)) := by
    simpa only [finrank_euclideanSpace,Fintype.card_prod,pow_two] using hcard
  let b : OrthonormalBasis K ℂ (EuclideanSpace ℂ (I × I)) :=
    OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' hc).ge
  have hb : ∀ k,b k=unitaryBellVector (W k) := by
    intro k
    exact congrFun (OrthonormalBasis.coe_mk hv _) k
  have he : weightedBellMatrix W (fun _ => 1)=1 := by
    apply Matrix.toEuclideanCLM.injective
    rw [map_one]
    apply ContinuousLinearMap.ext
    intro x
    change rectangularEuclideanCLM (weightedBellMatrix W (fun _ => 1)) x=x
    rw [weightedBellMatrix_apply]
    simpa only [hb,Complex.ofReal_one,one_mul] using b.sum_repr' x
  simpa only [weightedBellMatrix,Complex.ofReal_one,one_smul,unitaryBellProjector] using he

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
/-- The Bell projector of the actual finite tensor matrix is the tensor of the actual local Bell projectors. -/
theorem unitaryBellProjector_tensor (A : S → Matrix I I ℂ) :
    unitaryBellProjector (wickTensorMatrix A)=pairedTensorMatrix (fun s => unitaryBellProjector (A s)) := by
  ext p q
  simp only [unitaryBellProjector_apply,pairedTensorMatrix,wickTensorMatrix,
    star_prod,Finset.prod_mul_distrib,Finset.prod_div_distrib,Fintype.card_fun,
    Nat.cast_pow,Finset.prod_const,Finset.card_univ]

omit [DecidableEq K] [DecidableEq I] in
/-- Actual tensor Bell matrices for product weights, on the same global pair coordinates. -/
theorem weightedBellMatrix_tensor (W : K → Matrix I I ℂ) (a : S → K → ℝ) :
    weightedBellMatrix (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
      (fun w => ∏ s,a s (w s)) = pairedTensorMatrix (fun s => weightedBellMatrix W (a s)) := by
  change (∑ w : S → K,((∏ s,a s (w s):ℝ):ℂ) •
    unitaryBellProjector (wickTensorMatrix (fun s => W (w s))))=_
  simp only [unitaryBellProjector_tensor]
  ext p q
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,pairedTensorMatrix,
    weightedBellMatrix,unitaryBellProjector,Complex.ofReal_prod]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun s k => (a s k:ℂ)*unitaryBellProjector (W k)
    (p.1 s,p.2 s) (q.1 s,q.2 s))).symm

end CertificationGaussian
