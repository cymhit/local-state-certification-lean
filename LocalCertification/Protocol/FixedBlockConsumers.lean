import LocalCertification.Protocol.FixedBlockLogCriterion

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.FixedBlockConsumers

/-- An explicit physical partition exists at every size; its permutation stays fixed across copies. -/
def standardPartition (k m : ℕ) : FixedBlockPartition k m :=
  (finCongr (Nat.mul_comm k m)).trans finProdFinEquiv.symm

/-- The entire arbitrary within-block unitary group is retained, including entangled block bases. -/
theorem arbitrary_two_qubit_basis
    (V : ↥(unitary (Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ))) :
    ∃ U : LocalUnitary 4,unitaryReindex (blockLabelEquiv 2).symm U=V :=
  fixedBlock_local_basis_surjective 2 V

/-- A zero-block system still has the full actual trajectory law with the original seed and rules. -/
theorem empty_system_law {Z : Type*} [MeasurableSpace Z] (k : ℕ)
    (Q : FixedBlockProtocol Z k 0) (ρ : QIT.State (QuditIndex 2 (k*0))) :
    fixedBlockExecutionLaw (standardPartition k 0) Q ρ=
      executionLaw Q (ρ.reindex (fixedBlockIndexEquiv (standardPartition k 0))) :=
  fixedBlockExecutionLaw_eq (standardPartition k 0) Q ρ

/-- The threshold equality really has degree one, while a strictly larger gap has degree zero. -/
theorem two_qubit_block_boundary :
    criticalDegree 5 (1/5)=1 ∧ criticalDegree 5 (1/4)=0 := by
  constructor
  · have h := fixedBlock_degree_at_threshold 2 (by norm_num)
    norm_num at h ⊢
    exact h
  · have h := (fixedBlock_degree_zero_iff 2 (by norm_num) (1/4) (by norm_num)).mpr (by norm_num)
    norm_num at h ⊢
    exact h

/-- The explicit O(1+log(1/g)) block choice supplies an actual constant-log physical budget,
with no hidden existence hypothesis for the protocol or the Haar-typical sets. -/
theorem explicit_block_log_budget (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (P : (m : ℕ) → FixedBlockPartition (sufficientBlockSize ((a-b)/(1-b))) m) :
    ∃ good : (m : ℕ) → Set (sphere
        (0 : EuclideanSpace ℂ (QuditIndex 2 (sufficientBlockSize ((a-b)/(1-b))*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure
        (EuclideanSpace ℂ (QuditIndex 2 (sufficientBlockSize ((a-b)/(1-b))*m))) (good m)) atTop (nhds 1) ∧
      FixedBlockLogBound P good a b := by
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr (hab.trans_le ha))
  obtain ⟨_c,_C,_hc,_hC,good,hcompact,hprob,_hbound,hiff⟩ :=
    fixedBlock_corollary_six_two _ (sufficientBlockSize_positive _) P a b hb hab ha
  exact ⟨good,hcompact,hprob,hiff.mpr (sufficientBlockSize_threshold _ hg)⟩

/-- In the physical gap range the precise logarithmic size bound has no max truncation. -/
theorem sufficient_block_size_physical_gap (g : ℝ) (hg : 0<g) (hg1 : g≤1) :
    (sufficientBlockSize g : ℝ)≤1+Real.log (1/g)/Real.log 2 := by
  have hl : 0≤Real.log (1/g)/Real.log 2 :=
    div_nonneg (Real.log_nonneg ((one_le_div hg).mpr hg1)) (Real.log_pos (by norm_num)).le
  simpa only [max_eq_right hl] using sufficientBlockSize_log_bound g

end LocalCertification.Protocol.FixedBlockConsumers
