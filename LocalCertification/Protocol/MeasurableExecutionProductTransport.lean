import LocalCertification.Protocol.MeasurableExecutionTransport
import LocalCertification.Protocol.MeasurableExecutionBudgets
import LocalCertification.Quantum.MeasurablePOVMProductMap

/-! Local-product representation changes and the actual basis subclass in every
universe. The general protocol optimization never uses a finite-tree reduction. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u v
variable {d n : ℕ} [NeZero d]
  {Z S : Type u} {Ω : Fin n → Type u}
  {Z' S' : Type v} {Ω' : Fin n → Type v}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
  [MeasurableSpace Z'] [MeasurableSpace S'] [∀ i, MeasurableSpace (Ω' i)]

namespace ProductProtocol

omit [NeZero d] in
private theorem born_ext {P Q : BornProtocol Z S ((i : Fin n) → Ω i)
    (CertificationGaussian.QuditIndex d n)}
    (hr : P.toRawProtocol = Q.toRawProtocol) (hm : P.measurements = Q.measurements) : P = Q := by
  cases P
  cases Q
  cases hr
  cases hm
  rfl

def transport (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) : ProductProtocol d n Z' S' Ω' where
  toRawProtocol := (Transport.bornProtocol eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn).toRawProtocol
  localFamilies i := ((P.localFamilies i).map (eΩ i) (eΩ i).measurable).reindex eS.symm eS.symm.measurable

theorem transport_toBorn (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) :
    (transport eZ eS eΩ P).toBorn =
      Transport.bornProtocol eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn := by
  refine born_ext (P := (transport eZ eS eΩ P).toBorn)
    (Q := Transport.bornProtocol eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn) rfl ?_
  apply POVMKernel.ext_measurement
  intro s
  exact MeasurablePOVM.product_map_equiv (fun i => (P.localFamilies i).measurement (eS.symm s)) eΩ

theorem transport_law (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (transport eZ eS eΩ P).toBorn.law ρ = (P.toBorn.law ρ).map
      (fun p => (eZ p.1, fun m => Sum.map id (fun x i => eΩ i (x i)) (p.2 m))) := by
  rw [transport_toBorn]
  exact Transport.bornProtocol_law eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn ρ

theorem transport_expectedCopies (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (transport eZ eS eΩ P).toBorn.expectedCopies ρ = P.toBorn.expectedCopies ρ := by
  rw [transport_toBorn]
  exact Transport.bornProtocol_expectedCopies eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn ρ

theorem transport_valid_iff (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) : (transport eZ eS eΩ P).toBorn.Valid ψ a b δ ↔ P.toBorn.Valid ψ a b δ := by
  rw [transport_toBorn]
  exact Transport.bornProtocol_valid_iff eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn ψ a b δ

theorem transport_capped_iff (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) (N : ℕ) :
    (transport eZ eS eΩ P).toBorn.Capped N ↔ P.toBorn.Capped N := by
  rw [transport_toBorn]
  exact Transport.bornProtocol_capped_iff eZ eS (MeasurableEquiv.piCongrRight eΩ) P.toBorn N

def liftUniverse (P : ProductProtocol d n Z S Ω) :
    ProductProtocol d n (ULift.{v} Z) (ULift.{v} S) (fun i => ULift.{v} (Ω i)) :=
  transport MeasurableEquiv.ulift.symm MeasurableEquiv.ulift.symm
    (fun _ => MeasurableEquiv.ulift.symm) P

theorem liftUniverse_expectedCopies (P : ProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.liftUniverse.{u,v}.toBorn.expectedCopies ρ = P.toBorn.expectedCopies ρ :=
  transport_expectedCopies _ _ _ P ρ

theorem liftUniverse_valid_iff (P : ProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    P.liftUniverse.{u,v}.toBorn.Valid ψ a b δ ↔ P.toBorn.Valid ψ a b δ :=
  transport_valid_iff _ _ _ P ψ a b δ

theorem liftUniverse_capped_iff (P : ProductProtocol d n Z S Ω) (N : ℕ) :
    P.liftUniverse.{u,v}.toBorn.Capped N ↔ P.toBorn.Capped N :=
  transport_capped_iff _ _ _ P N

end ProductProtocol

theorem exists_product_transport (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : ∀ i, Ω i ≃ᵐ Ω' i)
    (P : ProductProtocol d n Z S Ω) :
    ∃ Q : ProductProtocol d n Z' S' Ω',
      Q.seedLaw = P.seedLaw.map eZ ∧
      (∀ i s, (Q.localFamilies i).measurement s =
        ((P.localFamilies i).measurement (eS.symm s)).map (eΩ i) (eΩ i).measurable) ∧
      (∀ ρ, Q.toBorn.law ρ = (P.toBorn.law ρ).map
        (fun p => (eZ p.1, fun m => Sum.map id (fun x i => eΩ i (x i)) (p.2 m)))) ∧
      (∀ ρ, Q.toBorn.expectedCopies ρ = P.toBorn.expectedCopies ρ) ∧
      (∀ ψ a b δ, Q.toBorn.Valid ψ a b δ ↔ P.toBorn.Valid ψ a b δ) ∧
      (∀ N, Q.toBorn.Capped N ↔ P.toBorn.Capped N) :=
  ⟨P.transport eZ eS eΩ, rfl, fun _ _ => rfl, ProductProtocol.transport_law eZ eS eΩ P,
    ProductProtocol.transport_expectedCopies eZ eS eΩ P, ProductProtocol.transport_valid_iff eZ eS eΩ P,
    ProductProtocol.transport_capped_iff eZ eS eΩ P⟩

namespace ProductBudget

theorem basis_capFeasible_universe {Z₀ : Type} [MeasurableSpace Z₀] (P : QuditProtocol Z₀ d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : Protocol.Valid P ψ a b δ) (N : ℕ) (hc : Protocol.Capped P N) :
    capFeasible.{u} ψ a b δ N := by
  let Q := (basisProductProtocol P).liftUniverse.{0,u}
  refine capFeasible_of_protocol Q ψ a b δ ?_ N ?_
  · apply (ProductProtocol.liftUniverse_valid_iff _ ψ a b δ).mpr
    rw [basisProductProtocol_toBorn]
    exact (basisProtocol_valid_iff P ψ a b δ).mpr hv
  · apply (ProductProtocol.liftUniverse_capped_iff _ N).mpr
    rw [basisProductProtocol_toBorn]
    exact (basisProtocol_capped_iff P N).mpr hc

theorem expectedBudget_le_basisBudget_universe
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    expectedBudget.{u} ψ a b δ ≤ Protocol.expectedBudget ψ a b δ := by
  apply le_iInf
  intro P
  apply le_iInf
  intro hv
  let Q := (basisProductProtocol P.toRaw).liftUniverse.{0,u}
  have hvalid : Q.toBorn.Valid ψ a b δ := by
    apply (ProductProtocol.liftUniverse_valid_iff _ ψ a b δ).mpr
    rw [basisProductProtocol_toBorn]
    exact (basisProtocol_valid_iff P.toRaw ψ a b δ).mpr hv
  have hcost : protocolCost Q ψ a b = Protocol.protocolCost P.toRaw ψ a b := by
    unfold protocolCost Protocol.protocolCost
    apply congrArg iSup
    funext ρ
    change (basisProductProtocol P.toRaw).liftUniverse.{0,u}.toBorn.expectedCopies ρ.val = _
    rw [ProductProtocol.liftUniverse_expectedCopies, basisProductProtocol_toBorn, basisProtocol_expectedCopies]
  exact (expectedBudget_le_protocolCost Q ψ a b δ hvalid).trans_eq hcost

theorem maximumBudget_le_basisBudget_universe
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    maximumBudget.{u} ψ a b δ ≤ Protocol.maximumBudget ψ a b δ := by
  by_cases ht : Protocol.maximumBudget ψ a b δ = ⊤
  · rw [ht]
    exact le_top
  · obtain ⟨N, hN, Q, hv, hc⟩ := Protocol.maximumBudget_attained ψ a b δ ht
    rw [hN]
    exact maximumBudget_le_of_feasible ψ a b δ N (basis_capFeasible_universe Q.toRaw ψ a b δ hv N hc)

end ProductBudget

theorem product_budget_universe_basis_upper
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    ProductBudget.expectedBudget.{u} ψ a b δ ≤ Protocol.expectedBudget ψ a b δ ∧
      ProductBudget.maximumBudget.{u} ψ a b δ ≤ Protocol.maximumBudget ψ a b δ :=
  ⟨ProductBudget.expectedBudget_le_basisBudget_universe ψ a b δ,
    ProductBudget.maximumBudget_le_basisBudget_universe ψ a b δ⟩

end LocalCertification.Protocol.MeasurableExecution
