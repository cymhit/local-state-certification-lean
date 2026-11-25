import LocalCertification.Protocol.BornExecution

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- Read only the actual outcome component; empty padding remains empty. -/
def paddedOutcome : PaddedRecord S O → Option O := Sum.elim (fun _ => none) (fun r => some r.2)

omit [Inhabited S] [Inhabited O] in
theorem paddedOutcome_measurable [Fintype O] [MeasurableSingletonClass O] :
    Measurable (paddedOutcome (S := S) (O := O)) :=
  measurable_const.sumElim ((measurable_of_countable Option.some).comp measurable_snd)

/-- A total measurable decoder for full public histories; no claim that arbitrary decoded histories are legal. -/
def decodeRecords : (m : ℕ) → Z × (Fin m → PaddedRecord S O) → SlotHistory Z O m
  | 0 => fun p => ULift.up p.1
  | m+1 => fun p => (decodeRecords m (p.1, fun i => p.2 i.castSucc), paddedOutcome (p.2 (Fin.last m)))

omit [Inhabited S] [Inhabited O] in
theorem decodeRecords_measurable [Fintype O] [MeasurableSingletonClass O] (m : ℕ) :
    Measurable (decodeRecords (Z := Z) (S := S) (O := O) m) := by
  induction m with
  | zero => exact measurable_up.comp measurable_fst
  | succ m ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_pi_iff.mpr
      (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)))).prodMk
      (paddedOutcome_measurable.comp ((measurable_pi_apply (Fin.last m)).comp measurable_snd))

omit [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O] [Inhabited S] [Inhabited O] in
theorem decodeRecords_snoc (m : ℕ) (z : Z) (v : Fin m → PaddedRecord S O) (r : PaddedRecord S O) :
    decodeRecords (m+1) (z, Fin.snoc v r) = (decodeRecords m (z,v), paddedOutcome r) := by
  simp only [decodeRecords, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1

/-- Public histories retain seed, all complete setting/outcome records, padding flags, and next action/decision. -/
def publicPrefix (R : RawRules Z S O) (m : ℕ) (h : SlotHistory Z O m) : Z × ExecutionState S O m :=
  (slotSeed m h, execPrefix R m h)

def decodePublicPrefix (m : ℕ) (p : Z × ExecutionState S O m) : SlotHistory Z O m :=
  decodeRecords m (p.1,p.2.1)

theorem publicPrefix_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    Measurable (publicPrefix R m) := (slotSeed_measurable m).prodMk (execPrefix_measurable R m)

omit [Inhabited S] [Inhabited O] in
theorem decodePublicPrefix_measurable [Fintype O] [MeasurableSingletonClass O] (m : ℕ) :
    Measurable (decodePublicPrefix (Z := Z) (S := S) (O := O) m) :=
  (decodeRecords_measurable m).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

/-- Reconstruction is asserted exactly on consistent histories, not on arbitrary raw slots after stopping. -/
theorem decodePublicPrefix_publicPrefix (R : RawRules Z S O) (m : ℕ) (h : SlotHistory Z O m)
    (hc : ConsistentPrefix R m h) : decodePublicPrefix m (publicPrefix R m h) = h := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨h,o⟩ := h
    have hi := ih h hc.1
    change decodeRecords (m+1) (slotSeed m h, (advance R (slotSeed m h) (execPrefix R m h) o).1) = (h,o)
    by_cases ha : h ∈ activePrefix R m
    · have hs := hc.2.mpr ha
      cases o with
      | none => exact False.elim (hs rfl)
      | some x =>
        have ha' : actionContinues (execPrefix R m h).2 = true := ha
        simp only [advance, ite_eq_left ha', appendOutcome, decodeRecords_snoc, paddedOutcome]
        exact congrArg (fun h' => (h',some x)) hi
    · have ho : o = none := not_not.mp (fun hn => ha (hc.2.mp hn))
      have ha' : ¬actionContinues (execPrefix R m h).2 = true := ha
      simp only [advance, ite_eq_right ha', appendEmpty, decodeRecords_snoc, paddedOutcome]
      exact Prod.ext hi ho.symm

/-- The full singular KL is unchanged by any measurable representation with a left inverse a.e. in both worlds. -/
theorem klDiv_map_retract_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] (F : X → Y) (G : Y → X)
    (hF : Measurable F) (hG : Measurable G)
    (hP : ∀ᵐ x ∂P, G (F x) = x) (hQ : ∀ᵐ x ∂Q, G (F x) = x) :
    klDiv (P.map F) (Q.map F) = klDiv P Q := by
  have heP : (P.map F).map G = P := by
    rw [Measure.map_map hG hF, Measure.map_congr (show G ∘ F =ᵐ[P] id from hP), Measure.map_id]
  have heQ : (Q.map F).map G = Q := by
    rw [Measure.map_map hG hF, Measure.map_congr (show G ∘ F =ᵐ[Q] id from hQ), Measure.map_id]
  apply le_antisymm (klDiv_map_le P Q hF)
  simpa only [heP,heQ] using klDiv_map_le (P.map F) (Q.map F) hG

/-- Complete public records and primitive slots have exactly the same finite-horizon information.
The probability-one consistency needed for reconstruction is proved from each world's actual kernels. -/
theorem publicPrefix_klDiv [Fintype O] [MeasurableSingletonClass O]
    (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (m : ℕ) :
    klDiv ((prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m).map
      (publicPrefix R m))
      ((prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (η t)) m).map
      (publicPrefix R m)) =
    klDiv (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m)
      (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (η t)) m) := by
  apply klDiv_map_retract_ae _ _ (publicPrefix R m) (decodePublicPrefix m)
    (publicPrefix_measurable R m) (decodePublicPrefix_measurable m)
  · filter_upwards [prefixLaw_ae_consistent R ν κ m] with h hh
    exact decodePublicPrefix_publicPrefix R m h hh
  · filter_upwards [prefixLaw_ae_consistent R ν η m] with h hh
    exact decodePublicPrefix_publicPrefix R m h hh

end LocalCertification.Protocol
