import LocalCertification.Protocol.FixedHorizon
import LocalCertification.Protocol.BehaviorTree
import LocalCertification.Protocol.RawLawExt

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {H : Type u} {S : Type v} {O : Type w}
  [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace O]
  [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- A finite physical outcome word is totalized only beyond the fixed measurement horizon. -/
def fixedWordStream (N : ℕ) (x : Fin N → O) (t : ℕ) : O :=
  if h : t < N then x ⟨t,h⟩ else default

omit [MeasurableSpace H] [MeasurableSpace S] [Inhabited S] in
theorem fixedWordStream_measurable (N : ℕ) : Measurable (fixedWordStream (O := O) N) :=
  measurable_of_countable _

/-- Execute the real raw fixed-horizon rules on the original full seed and a physical outcome word. -/
def fixedWordPrefix (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict) (m : ℕ)
    (p : (Fin N → H) × (Fin N → O)) : SlotHistory (Fin N → H) O m :=
  logicalPrefix (fixedHorizonRules N setting hs verdict hv) p.1 (fixedWordStream N p.2) m

theorem fixedWordPrefix_measurable (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict) (m : ℕ) :
    Measurable (fixedWordPrefix N setting hs verdict hv m) :=
  (logicalPrefix_measurable _ m).comp (measurable_fst.prodMk
    ((fixedWordStream_measurable N).comp measurable_snd))

omit [Fintype O] [MeasurableSingletonClass O] in
theorem fixedWordPrefix_succ (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (m : ℕ) (hm : m < N) (p : (Fin N → H) × (Fin N → O)) :
    fixedWordPrefix N setting hs verdict hv (m+1) p =
      (fixedWordPrefix N setting hs verdict hv m p, some (p.2 ⟨m,hm⟩)) := by
  change (_, if runContinues (fixedHorizonRules N setting hs verdict hv) p.1 (fixedWordStream N p.2) m
    then some (fixedWordStream N p.2 m) else none) = _
  rw [ite_eq_left ((fixedHorizon_runContinues_iff _ _ _ _ _ _ _ _).mpr hm)]
  simp only [fixedWordStream, dite_eq_left hm]
  rfl

omit [Fintype O] [MeasurableSingletonClass O] in
theorem fixedWordPrefix_active (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (m : ℕ) (hm : m < N) (p : (Fin N → H) × (Fin N → O)) :
    fixedWordPrefix N setting hs verdict hv m p ∈ activePrefix (fixedHorizonRules N setting hs verdict hv) m :=
  (fixedHorizon_runContinues_iff _ _ _ _ _ _ _ _).mpr hm

omit [Fintype O] [MeasurableSingletonClass O] in
theorem fixedWordPrefix_setting (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (m : ℕ) (hm : m < N) (p : (Fin N → H) × (Fin N → O)) :
    prefixSetting (fixedHorizonRules N setting hs verdict hv) m
      (fixedWordPrefix N setting hs verdict hv m p) = setting (p.1 ⟨m,hm⟩) :=
  fixedHorizon_runSetting _ _ _ _ _ _ _ _ hm

omit [Fintype O] [MeasurableSingletonClass O] in
/-- A prefix is unaffected by refreshing an unobserved coordinate, pointwise even on zero-mass words. -/
theorem fixedWordPrefix_update (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (m : ℕ) (i : Fin N) (hmi : m ≤ i.val) (p : (Fin N → H) × (Fin N → O)) (o : O) :
    fixedWordPrefix N setting hs verdict hv m (p.1,Function.update p.2 i o) =
      fixedWordPrefix N setting hs verdict hv m p := by
  apply logicalPrefix_congr_prefix
  intro k hk
  have hkN : k < N := lt_trans (lt_of_lt_of_le hk hmi) i.isLt
  simp only [fixedWordStream, dite_eq_left hkN]
  apply Function.update_of_ne
  intro he
  have he' := congrArg Fin.val he
  change k = i.val at he'
  omega

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Every finite primitive slot before stopping is exactly the corresponding actual outcome. -/
theorem historySlot_fixedWordPrefix (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (m : ℕ) (hm : m ≤ N) (p : (Fin N → H) × (Fin N → O)) (i : Fin m) :
    historySlot m (fixedWordPrefix N setting hs verdict hv m p) i =
      some (p.2 ⟨i.val,lt_of_lt_of_le i.isLt hm⟩) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [fixedWordPrefix_succ _ _ _ _ _ m (by omega)]
    cases i using Fin.lastCases with
    | last => simp [historySlot]
    | cast i => simpa only [historySlot, Fin.lastCases_castSucc, Fin.val_castSucc] using ih (by omega) i

/-- Decode the complete original seed and all N physical outcomes from the primitive finite prefix. -/
def fixedWordDecode (N : ℕ) (h : SlotHistory (Fin N → H) O N) : (Fin N → H) × (Fin N → O) :=
  (slotSeed N h, fun i => (historySlot N h i).getD default)

omit [MeasurableSpace S] [Inhabited S] [MeasurableSingletonClass O] in
theorem fixedWordDecode_measurable (N : ℕ) : Measurable (fixedWordDecode (H := H) (O := O) N) :=
  (slotSeed_measurable N).prodMk (measurable_pi_iff.mpr (fun i =>
    (measurable_of_countable (fun x : Option O => x.getD default)).comp (historySlot_measurable N i)))

omit [Fintype O] [MeasurableSingletonClass O] in
/-- This inverse is proved on the entire finite-word simulation image; no law-a.e. inverse is postulated. -/
theorem fixedWordDecode_prefix (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (p : (Fin N → H) × (Fin N → O)) :
    fixedWordDecode N (fixedWordPrefix N setting hs verdict hv N p) = p := by
  apply Prod.ext
  · exact logicalPrefix_seed _ _ _ _
  · funext i
    change (historySlot N (fixedWordPrefix N setting hs verdict hv N p) i).getD default = p.2 i
    rw [historySlot_fixedWordPrefix _ _ _ _ _ N le_rfl p i]
    rfl

end LocalCertification.Protocol
