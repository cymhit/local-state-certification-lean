import LocalCertification.Paper
import LocalCertification.Quantum.MeasurablePOVMRankOne
import LocalCertification.Quantum.MeasurablePOVMProductInformation
import LocalCertification.Quantum.BinaryStateMixture
import LocalCertification.Protocol.MeasurableHistoryBudgets

open MeasureTheory Matrix
open LocalCertification.Quantum
open scoped ComplexOrder MatrixOrder ENNReal
noncomputable section
namespace MeasurableRefinementExamples
def uniformInterval : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
instance : IsProbabilityMeasure uniformInterval where
  measure_univ := by simp [uniformInterval]
def M : MeasurablePOVM ℝ (Fin 2) := MeasurablePOVM.ofProbability uniformInterval

example (ρ : QIT.State (Fin 2)) :
    (M.refinedPOVM.born ρ).map Prod.fst = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  rw [M.refinedPOVM_born_map_fst]
  exact MeasurablePOVM.born_ofProbability uniformInterval ρ

example : M.refinementReference.map Prod.fst = uniformInterval := by
  rw [M.refinementReference_map_fst]
  exact MeasurablePOVM.traceReference_ofProbability uniformInterval

example (p : ℝ × Fin 2) :
    ∃ ψ : QIT.PureVector (Fin 2), ψ.state.matrix = M.refinementProjector p.1 p.2 :=
  M.refinementProjector_eq_pure p.1 p.2

example (p : ℝ × Fin 2) :
    M.refinementProjector p.1 p.2 * M.refinementProjector p.1 p.2 = M.refinementProjector p.1 p.2 :=
  M.refinementProjector_mul_self p.1 p.2

example (p : ℝ × Fin 2) : M.refinedBornDensity (QIT.State.maximallyMixed (Fin 2)) p = 1 :=
  M.refinedBornDensity_maximallyMixed p
end MeasurableRefinementExamples

open MeasureTheory Matrix InformationTheory LocalCertification.Quantum
open scoped ENNReal ComplexOrder MatrixOrder
noncomputable section
namespace ProductInformationExamples
def uniformInterval : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
instance : IsProbabilityMeasure uniformInterval where
  measure_univ := by simp [uniformInterval]
def locals : Fin 2 → MeasurablePOVM ℝ (Fin 2) :=
  fun _ => MeasurablePOVM.ofProbability uniformInterval
def noisy (τ : QIT.State (Fin 2 → Fin 2)) : QIT.State (Fin 2 → Fin 2) :=
  binaryMixture (QIT.State.maximallyMixed (Fin 2 → Fin 2)) τ (1/2) (by norm_num) (by norm_num)
theorem noisy_floor (τ : QIT.State (Fin 2 → Fin 2)) :
    ((noisy τ).matrix - (1/2 : ℝ) • (QIT.State.maximallyMixed (Fin 2 → Fin 2)).matrix).PosSemidef := by
  have hf : ((QIT.State.maximallyMixed (Fin 2 → Fin 2)).matrix -
      (1 : ℝ) • (QIT.State.maximallyMixed (Fin 2 → Fin 2)).matrix).PosSemidef := by
    simpa only [one_smul, sub_self] using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ).PosSemidef)
  have h := binaryMixture_floor (QIT.State.maximallyMixed (Fin 2 → Fin 2)) τ
    (QIT.State.maximallyMixed (Fin 2 → Fin 2)) (1/2) 1 (by norm_num) (by norm_num) hf
  convert h using 1
  norm_num [noisy]
example (ρ τ : QIT.State (Fin 2 → Fin 2)) :
    klDiv ((MeasurablePOVM.product locals).born ρ) ((MeasurablePOVM.product locals).born (noisy τ)) ≤
      ENNReal.ofReal ((1/2 : ℝ)⁻¹ * (Fintype.card (Fin 2 → Fin 2) : ℝ)^2 *
        ∫ p, (((ρ.matrix - (noisy τ).matrix) * MeasurablePOVM.productRefinementProjector locals p).trace.re)^2
          ∂MeasurablePOVM.productRefinementReference locals) :=
  MeasurablePOVM.product_born_klDiv_le_tensor_sq locals ρ (noisy τ) (1/2) (by norm_num) (noisy_floor τ)
end ProductInformationExamples

#eval IO.println "MeasurementModelRegression_PASS"

/- The direct history model and the existing setting model have the same
extended budgets in every declared universe, on arbitrary measurable spaces. -/
namespace HistoryCompilerExamples
open LocalCertification.Protocol.MeasurableExecution
universe u
variable {d n : ℕ} [NeZero d]

example (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    PaperHistoryBudget.expectedBudget.{u} ψ a b δ = ProductBudget.expectedBudget.{u} ψ a b δ ∧
    PaperHistoryBudget.maximumBudget.{u} ψ a b δ = ProductBudget.maximumBudget.{u} ψ a b δ ∧
    ∀ N, PaperHistoryBudget.capFeasible.{u} ψ a b δ N ↔ ProductBudget.capFeasible.{u} ψ a b δ N :=
  LocalCertification.Paper.history_budget_equivalence ψ a b δ

variable {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]

/-- Joint outcomes are evaluated against the full input state. Only the trace
reference measure factorizes across sites. -/
example (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (MeasurablePOVM.product M).born ρ =
      (Measure.pi (fun i => (M i).traceReference)).withDensity (fun x =>
        ENNReal.ofReal ((ρ.matrix * tensorMatrix (fun i => (M i).traceDensity (x i))).trace.re)) :=
  MeasurablePOVM.product_born_eq_withDensity M ρ

example (P : PaperHistoryProduct d n Z L Ω) (N : ℕ) (hc : P.Capped N)
    (p : Sample Z (Slot ((i : Fin n) → Ω i))) (hp : Legal P.raw.toRawRules p) :
    P.time p ≤ (N : ℕ∞) := hc p hp

/- The source protocol's own iterated law and extended copy count appear in
the bound. No finite-expectation premise or probability-one cap is introduced. -/
example (P : PaperHistoryProduct d n Z L Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) :
    ProductBudget.expectedBudget.{u} ψ a b δ ≤
      ⨆ ρ : ProductBudget.promisedStates ψ a b,
        ∫⁻ p, ENat.toENNReal (P.time p) ∂P.law ρ.val :=
  P.expectedBudget_le_protocolCost ψ a b δ hv

example (P : PaperHistoryProduct d n Z L Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) (N : ℕ) (hc : P.Capped N) :
    ProductBudget.capFeasible.{u} ψ a b δ N ∧
      ProductBudget.maximumBudget.{u} ψ a b δ ≤ (N : ℕ∞) :=
  ⟨P.capFeasible_of_capped ψ a b δ hv N hc, P.maximumBudget_le_cap ψ a b δ hv N hc⟩

/- If no context continues, an empty setting type suffices even if the outcome
spaces admit no normalized POVM. The equality is proved for every state. -/
example (P : PaperHistoryProduct d n Z L Ω)
    (hn : ¬ ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}) :
    ∃ Q : ProductProtocol d n Z PEmpty.{u+1} Ω,
      P.Preserves Q ∧ ∀ ρ, Q.toBorn.expectedCopies ρ = P.expectedCopies ρ :=
  ⟨P.emptyCompile, P.emptyCompile_preserves hn,
    (P.emptyCompile_preserves hn).expectedCopies_eq⟩

/-- An infinite optimum is exactly the case in which no natural-number cap
is feasible. Any finite optimum is attained on every legal path. -/
example (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    (ProductBudget.maximumBudget.{u} ψ a b δ = ⊤ ↔
      ¬ ∃ m : ℕ, ProductBudget.capFeasible.{u} ψ a b δ m) ∧
    (ProductBudget.maximumBudget.{u} ψ a b δ ≠ ⊤ →
      ∃ m : ℕ, ProductBudget.maximumBudget.{u} ψ a b δ = (m : ℕ∞) ∧
        ProductBudget.capFeasible.{u} ψ a b δ m) :=
  ⟨ProductBudget.maximumBudget_eq_top_iff ψ a b δ,
    ProductBudget.maximumBudget_attained ψ a b δ⟩

example (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hempty : ∀ (Z S : Type u) (Ω : Fin n → Type u) [MeasurableSpace Z] [MeasurableSpace S]
      [∀ i, MeasurableSpace (Ω i)] (P : ProductProtocol d n Z S Ω), ¬ P.toBorn.Valid ψ a b δ) :
    ProductBudget.expectedBudget.{u} ψ a b δ = ⊤ := by
  apply top_unique
  apply ProductBudget.expectedBudget_lower
  intro Z S Ω _ _ _ P hv
  exact (hempty Z S Ω P hv).elim

end HistoryCompilerExamples

#eval IO.println "HistoryModelRegression_PASS"
