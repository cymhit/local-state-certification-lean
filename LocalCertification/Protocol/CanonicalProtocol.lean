import LocalCertification.Protocol.TreeLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u

/-- A fixed small type of protocols: an arbitrary set of all behavior trees, together with a probability law on that subtype.
The set need not be Borel; the seed sigma algebra is the induced subtype sigma algebra. -/
abbrev CanonicalProtocol (d n : ℕ) : Type :=
  Σ R : Set (BehaviorTree (ProductSetting d n) (CertificationGaussian.QuditIndex d n)), ProbabilityMeasure R

variable {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Every canonical package is a genuine original raw protocol. Arbitrary trees need not themselves be absorbing. -/
def CanonicalProtocol.toRaw (Q : CanonicalProtocol d n) : QuditProtocol Q.1 d n where
  toRawRules := treeRules Q.1
  seedLaw := Q.2.toMeasure
  seed_probability := Q.2.prop

variable {Z : Type u} [MeasurableSpace Z]

/-- Full-image normalization from every original seed universe into the fixed small protocol type. -/
def normalizeProtocol (P : QuditProtocol Z d n) : CanonicalProtocol d n :=
  ⟨seedTreeImage P.toRawRules, ⟨P.seedLaw.map (seedToTree P.toRawRules), (imageTreeProtocol P).seed_probability⟩⟩

theorem normalizeProtocol_toRaw (P : QuditProtocol Z d n) :
    (normalizeProtocol P).toRaw = imageTreeProtocol P := rfl

theorem normalizeProtocol_valid_iff (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    Valid (normalizeProtocol P).toRaw ψ a b δ ↔ Valid P ψ a b δ :=
  imageTreeProtocol_valid_iff P ψ a b δ

theorem normalizeProtocol_capped_iff (P : QuditProtocol Z d n) (N : ℕ) :
    Capped (normalizeProtocol P).toRaw N ↔ Capped P N := imageTreeProtocol_capped_iff P N

theorem normalizeProtocol_expectedCopies (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    expectedCopies (normalizeProtocol P).toRaw ρ = expectedCopies P ρ := imageTreeProtocol_expectedCopies P ρ

/-- A constructive coverage theorem for budgets: one actual canonical package preserves all tasks,
all path caps, and every extended input cost simultaneously. No universe-sized infimum is required. -/
theorem canonical_protocol_coverage (P : QuditProtocol Z d n) :
    ∃ Q : CanonicalProtocol d n,
      (∀ ψ a b δ, Valid Q.toRaw ψ a b δ ↔ Valid P ψ a b δ) ∧
      (∀ N, Capped Q.toRaw N ↔ Capped P N) ∧
      (∀ ρ, expectedCopies Q.toRaw ρ = expectedCopies P ρ) :=
  ⟨normalizeProtocol P, normalizeProtocol_valid_iff P, normalizeProtocol_capped_iff P,
    normalizeProtocol_expectedCopies P⟩

end LocalCertification.Protocol
