import LocalCertification.Protocol.ConditionalBorn
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Topology.Algebra.Star.Unitary

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w z

/-- The coproduct uses the original sum sigma algebra, which agrees with its topological Borel algebra. -/
theorem sum_borelSpace {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro s hs
    obtain ⟨hA,hB⟩ := measurableSet_sum_iff.mp hs
    let : MeasurableSpace (A ⊕ B) := borel (A ⊕ B)
    let : BorelSpace (A ⊕ B) := ⟨rfl⟩
    have hl : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsOpenEmbedding.inl.measurableEmbedding.measurableSet_image.mpr hA
    have hr : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsOpenEmbedding.inr.measurableEmbedding.measurableSet_image.mpr hB
    have he : (Sum.inl '' (Sum.inl ⁻¹' s) : Set (A ⊕ B)) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
      ext x
      cases x <;> simp
    rw [← he]
    exact hl.union hr
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩

/-- The actual continuous product-unitary setting space is standard Borel, without assumptions on seeds. -/
theorem productSetting_standardBorel (d n : ℕ) : StandardBorelSpace (ProductSetting d n) := by
  let : PolishSpace (Matrix (Fin d) (Fin d) ℂ) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℂ))
  let : PolishSpace (CertificationGaussian.LocalUnitary d) := (isClosed_unitary (R := Matrix (Fin d) (Fin d) ℂ)).polishSpace
  infer_instance

/-- Only this finite-dimensional action target needs the standard-Borel property for pointwise factorization. -/
theorem quditAction_standardBorel (d n : ℕ) : StandardBorelSpace (Action (ProductSetting d n)) := by
  let : PolishSpace (Matrix (Fin d) (Fin d) ℂ) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℂ))
  let : PolishSpace (CertificationGaussian.LocalUnitary d) := (isClosed_unitary (R := Matrix (Fin d) (Fin d) ℂ)).polishSpace
  let : PolishSpace (ProductSetting d n) := inferInstanceAs (PolishSpace (Fin n → CertificationGaussian.LocalUnitary d))
  let : BorelSpace (Action (ProductSetting d n)) := sum_borelSpace
  infer_instance

/-- Assemble the stop-decision and continue-setting branches on the raw domain where the rule is called. -/
def filtrationAction {X : Type u} {S : Type v} (stop : Set X) (J : X → Fin 2) (U : X → S) : X → Action S := by
  classical
  exact fun x => if x ∈ stop then Sum.inl (J x) else Sum.inr (U x)

/-- Stopped measurability and predictable settings imply raw action measurability; this is not an input field. -/
theorem filtrationAction_measurable {X : Type u} {S : Type v} [MeasurableSpace X] [MeasurableSpace S]
    (stop : Set X) (J : X → Fin 2) (U : X → S) (hs : MeasurableSet stop)
    (hj : Measurable (fun x : stop => J x.val))
    (hu : Measurable (fun x : (stopᶜ : Set X) => U x.val)) : Measurable (filtrationAction stop J U) := by
  classical
  exact (measurable_inl.comp hj).dite (measurable_inr.comp hu) hs

/-- Pointwise raw-filtration factorization on every alive logical path. The domain is T≥m,
so earlier-stopped paths never feed a variable-length history to a fixed-length rule.
No measure, input state, almost-everywhere representative, or standard-Borel seed/history is involved. -/
theorem raw_filtration_rules_exist {Ω : Type z} {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [StandardBorelSpace (Action S)]
    (T : Ω → WithTop ℕ) (J : Ω → Fin 2) (U : ℕ → Ω → S)
    (H : (m : ℕ) → {ω : Ω | (m : WithTop ℕ) ≤ T ω} → Z × (Fin m → Record S O))
    (hs : ∀ m, MeasurableSet[MeasurableSpace.comap (H m) inferInstance]
      {ω | T ω.val = (m : WithTop ℕ)})
    (hj : ∀ m, Measurable[MeasurableSpace.comap Subtype.val (MeasurableSpace.comap (H m) inferInstance)]
      (fun ω : {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val = (m : WithTop ℕ)} => J ω.val.val))
    (hu : ∀ m, Measurable[MeasurableSpace.comap Subtype.val (MeasurableSpace.comap (H m) inferInstance)]
      (fun ω : {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val ≠ (m : WithTop ℕ)} => U m ω.val.val)) :
    ∃ R : RawRules Z S O, ∀ (m : ℕ) (ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω}),
      R.rule m (H m ω) = filtrationAction {ω | T ω.val = (m : WithTop ℕ)}
        (fun ω => J ω.val) (fun ω => U m ω.val) ω := by
  have hfactor (m : ℕ) : ∃ a : Z × (Fin m → Record S O) → Action S, Measurable a ∧
      filtrationAction {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val = (m : WithTop ℕ)}
        (fun ω => J ω.val) (fun ω => U m ω.val) = a ∘ H m := by
    let : MeasurableSpace {ω : Ω | (m : WithTop ℕ) ≤ T ω} := MeasurableSpace.comap (H m) inferInstance
    exact (filtrationAction_measurable {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val = (m : WithTop ℕ)}
      (fun ω => J ω.val) (fun ω => U m ω.val) (hs m) (hj m) (hu m)).exists_eq_measurable_comp
  choose a ha he using hfactor
  exact ⟨⟨a,ha⟩, fun m ω => (congrFun (he m) ω).symm⟩

/-- The factorization applies to the actual qudit action for every d,n, including the empty tensor boundary. -/
theorem qudit_raw_filtration_rules_exist {Ω : Type v} {Z : Type u} [MeasurableSpace Z] (d n : ℕ)
    (T : Ω → WithTop ℕ) (J : Ω → Fin 2) (U : ℕ → Ω → ProductSetting d n)
    (H : (m : ℕ) → {ω : Ω | (m : WithTop ℕ) ≤ T ω} → Z × (Fin m → Record (ProductSetting d n) (CertificationGaussian.QuditIndex d n)))
    (hs : ∀ m, MeasurableSet[MeasurableSpace.comap (H m) inferInstance] {ω | T ω.val = (m : WithTop ℕ)})
    (hj : ∀ m, Measurable[MeasurableSpace.comap Subtype.val (MeasurableSpace.comap (H m) inferInstance)]
      (fun ω : {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val = (m : WithTop ℕ)} => J ω.val.val))
    (hu : ∀ m, Measurable[MeasurableSpace.comap Subtype.val (MeasurableSpace.comap (H m) inferInstance)]
      (fun ω : {ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω} | T ω.val ≠ (m : WithTop ℕ)} => U m ω.val.val)) :
    ∃ R : RawRules Z (ProductSetting d n) (CertificationGaussian.QuditIndex d n),
      ∀ (m : ℕ) (ω : {ω : Ω | (m : WithTop ℕ) ≤ T ω}),
      R.rule m (H m ω) = filtrationAction {ω | T ω.val = (m : WithTop ℕ)}
        (fun ω => J ω.val) (fun ω => U m ω.val) ω := by
  let := quditAction_standardBorel d n
  exact raw_filtration_rules_exist T J U H hs hj hu

end LocalCertification.Protocol
