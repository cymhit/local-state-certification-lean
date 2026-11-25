import LocalCertification.Protocol.MeasurableExecutionBasis
import LocalCertification.Quantum.MeasurablePOVMProductKernel

/-! Admissible local-product protocols retain arbitrary measurable local
outcomes. Their executable global measurement is the actual local POVM
product, with no information inequality or concentration property as a field. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Quantum Matrix
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

structure ProductProtocol (d n : ℕ) (Z S : Type u) (Ω : Fin n → Type u)
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    extends RawProtocol Z S ((i : Fin n) → Ω i) where
  localFamilies : ∀ i : Fin n, POVMKernel S (Ω i) (Fin d)

namespace ProductProtocol
variable {d n : ℕ} [NeZero d] {Z S : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

/-- The actual global Born executor is constructed from the product of the
chosen original local measurements, including for entangled input states. -/
def toBorn (P : ProductProtocol d n Z S Ω) :
    BornProtocol Z S ((i : Fin n) → Ω i) (CertificationGaussian.QuditIndex d n) where
  toRawProtocol := P.toRawProtocol
  measurements := POVMKernel.product P.localFamilies

theorem toBorn_measurement (P : ProductProtocol d n Z S Ω) (s : S) :
    (P.toBorn.measurements).measurement s =
      MeasurablePOVM.product (fun i => (P.localFamilies i).measurement s) := rfl

theorem bornKernel_apply (P : ProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (s : S) :
    P.toBorn.measurements.bornKernel ρ s =
      (MeasurablePOVM.product (fun i => (P.localFamilies i).measurement s)).born ρ := rfl

end ProductProtocol

private theorem local_basis_effect_measurable (d n : ℕ) (i : Fin n) (x : Fin d) :
    Measurable (fun U : ProductSetting d n => (basisPOVM (U i)).effects x) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp_rw [basisPOVM_effect_rankOne, QIT.rankOneMatrix_apply]
  apply Continuous.measurable
  have hc (a : Fin d) : Continuous (fun U : ProductSetting d n => (U i).val a x) :=
    (continuous_apply x).comp ((continuous_apply a).comp
      ((continuous_subtype_val : Continuous (fun V : CertificationGaussian.LocalUnitary d => V.val)).comp
        (continuous_apply i)))
  exact (hc a).mul (hc b).star

def basisLocalFamily (d n : ℕ) (i : Fin n) : POVMKernel (ProductSetting d n) (Fin d) (Fin d) :=
  POVMKernel.ofFinite (fun U => basisPOVM (U i)) (local_basis_effect_measurable d n i)

theorem basisLocalFamily_measurement (d n : ℕ) (i : Fin n) (s : ProductSetting d n) :
    (basisLocalFamily d n i).measurement s = MeasurablePOVM.ofFinite (basisPOVM (s i)) := rfl

private theorem family_eq_of_measurements {H O I : Type*} [MeasurableSpace H] [MeasurableSpace O]
    [Fintype I] [DecidableEq I] (A B : POVMKernel H O I)
    (h : ∀ s, A.measurement s = B.measurement s) : A = B := by
  cases A with
  | mk ma ha =>
    cases B with
    | mk mb hb =>
      have he : ma = mb := funext h
      subst mb
      rfl

theorem product_basisLocalFamily (d n : ℕ) [NeZero d] :
    POVMKernel.product (basisLocalFamily d n) = POVMKernel.productBasis d n := by
  apply family_eq_of_measurements
  intro s
  rw [POVMKernel.product_measurement, POVMKernel.productBasis_measurement]
  rfl

variable {Z : Type} [MeasurableSpace Z] {d n : ℕ} [NeZero d]

def basisProductProtocol (P : QuditProtocol Z d n) :
    ProductProtocol d n Z (ProductSetting d n) (fun _ => Fin d) where
  toRawProtocol := P
  localFamilies := basisLocalFamily d n

theorem basisProductProtocol_toBorn (P : QuditProtocol Z d n) :
    (basisProductProtocol P).toBorn = basisProtocol P := by
  change BornProtocol.mk P (POVMKernel.product (basisLocalFamily d n)) =
    BornProtocol.mk P (POVMKernel.productBasis d n)
  rw [product_basisLocalFamily]

theorem exists_local_product_basis_embedding (P : QuditProtocol Z d n) :
    ∃ K : ∀ _i : Fin n, POVMKernel (ProductSetting d n) (Fin d) (Fin d),
      ∃ Q : BornProtocol Z (ProductSetting d n)
          (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n),
        Q.toRawProtocol = P ∧ Q.measurements = POVMKernel.product K ∧
        (∀ (s : ProductSetting d n) (i : Fin n),
          (K i).measurement s = MeasurablePOVM.ofFinite (basisPOVM (s i))) ∧
        (∀ ρ, Q.expectedCopies ρ = Protocol.expectedCopies P ρ) ∧
        (∀ ψ a b δ, Q.Valid ψ a b δ ↔ Protocol.Valid P ψ a b δ) ∧
        (∀ N, Q.Capped N ↔ Protocol.Capped P N) := by
  refine ⟨basisLocalFamily d n, (basisProductProtocol P).toBorn, rfl, rfl,
    fun _ _ => rfl, ?_, ?_, ?_⟩
  · rw [basisProductProtocol_toBorn]
    exact basisProtocol_expectedCopies P
  · rw [basisProductProtocol_toBorn]
    exact basisProtocol_valid_iff P
  · rw [basisProductProtocol_toBorn]
    exact basisProtocol_capped_iff P

end LocalCertification.Protocol.MeasurableExecution
