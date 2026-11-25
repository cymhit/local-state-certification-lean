import LocalCertification.Protocol.StoppingTime
import LocalCertification.Quantum.CompleteBornRecord

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {H : Type u} {S : Type v} {O : Type w}
  [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace O]

/-- A fixed-horizon protocol samples all labels at the start, requests their settings in order,
and then applies the prescribed measurable decision to the complete label/outcome records.
The rule is total on every raw history and has no state argument. -/
def fixedHorizonRules (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict) : RawRules (Fin N → H) S O where
  rule t p := if h : t < N then Sum.inr (setting (p.1 ⟨t,h⟩)) else
    Sum.inl (verdict (fun i => (p.1 i, (p.2 ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_not_gt h)⟩).2)))
  measurable_rule t := by
    by_cases h : t < N
    · simp only [dite_eq_left h]
      exact measurable_inr.comp (hs.comp ((measurable_pi_apply (⟨t,h⟩ : Fin N)).comp measurable_fst))
    · simp only [dite_eq_right h]
      apply measurable_inl.comp (hv.comp _)
      apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_pi_apply i).comp measurable_fst).prodMk
        (measurable_snd.comp ((measurable_pi_apply (⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_not_gt h)⟩ : Fin t)).comp measurable_snd))

/-- Independent seed labels are chosen before any physical measurement, without discarding any zero-mass seed. -/
def fixedHorizonProtocol (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] : RawProtocol (Fin N → H) S O where
  toRawRules := fixedHorizonRules N setting hs verdict hv
  seedLaw := Measure.pi (fun _ : Fin N => μ)
  seed_probability := inferInstance

theorem fixedHorizon_rule_continues_iff (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict) (t : ℕ)
    (p : (Fin N → H) × (Fin t → Record S O)) :
    actionContinues ((fixedHorizonRules N setting hs verdict hv).rule t p) = true ↔ t < N := by
  by_cases h : t < N <;> simp [fixedHorizonRules, h, actionContinues]

variable [Inhabited S] [Inhabited O]

/-- Every seed and every outcome stream requests exactly the first N copies, even on null paths. -/
theorem fixedHorizon_runContinues_iff (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) (t : ℕ) :
    runContinues (fixedHorizonRules N setting hs verdict hv) z x t ↔ t < N := by
  induction t with
  | zero => exact fixedHorizon_rule_continues_iff N setting hs verdict hv 0 _
  | succ t ih =>
    by_cases ht : t < N
    · have ha := ih.mpr ht
      simp only [runContinues, runState_succ_active _ z x t ha, appendOutcome]
      exact fixedHorizon_rule_continues_iff N setting hs verdict hv (t+1) _
    · have ha := mt ih.mp ht
      simp only [runContinues, runState_succ_stopped _ z x t ha, appendEmpty]
      change runContinues (fixedHorizonRules N setting hs verdict hv) z x t ↔ t+1 < N
      rw [ih]
      omega

theorem fixedHorizon_everyPathCap (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict) :
    EveryPathCap (fixedHorizonRules N setting hs verdict hv) N := by
  intro z x
  rw [fixedHorizon_runContinues_iff]
  exact Nat.lt_irrefl N

/-- The actual complete setting selected on a live run is its pre-sampled label's setting. -/
theorem fixedHorizon_runSetting (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) (t : ℕ) (ht : t < N) :
    actionSetting (runState (fixedHorizonRules N setting hs verdict hv) z x t).2 = setting (z ⟨t,ht⟩) := by
  rw [runState_action_eq_rule _ z x t ((fixedHorizon_runContinues_iff _ _ _ _ _ _ _ _).mpr ht)]
  simp [fixedHorizonRules, ht, actionSetting]

/-- All N physical records, including the record immediately before stopping, are retained exactly. -/
theorem fixedHorizon_runRecords (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) (t : ℕ) (ht : t ≤ N) :
    (runState (fixedHorizonRules N setting hs verdict hv) z x t).1 =
      fun i => Sum.inr (setting (z ⟨i.val,lt_of_lt_of_le i.isLt ht⟩), x i.val) := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
    have hlt : t < N := by omega
    rw [runState_succ_active _ z x t ((fixedHorizon_runContinues_iff _ _ _ _ _ _ _ _).mpr hlt)]
    simp only [appendOutcome, fixedHorizon_runSetting _ _ _ _ _ _ _ _ hlt]
    rw [ih (by omega)]
    funext i
    cases i using Fin.lastCases <;> simp

/-- The computed action uses precisely the complete actual pre-stop record, also at the first stopping time. -/
theorem fixedHorizon_runAction (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) (t : ℕ) (ht : t ≤ N) :
    (runState (fixedHorizonRules N setting hs verdict hv) z x t).2 =
      (fixedHorizonRules N setting hs verdict hv).rule t
        (z, fun i => (setting (z ⟨i.val,lt_of_lt_of_le i.isLt ht⟩), x i.val)) := by
  cases t with
  | zero =>
    apply congrArg (fun f => (fixedHorizonRules N setting hs verdict hv).rule 0 (z,f))
    funext i; exact Fin.elim0 i
  | succ t =>
    have hlt : t < N := by omega
    rw [runState_succ_active _ z x t ((fixedHorizon_runContinues_iff _ _ _ _ _ _ _ _).mpr hlt)]
    simp only [appendOutcome, fixedHorizon_runSetting _ _ _ _ _ _ _ _ hlt,
      fixedHorizon_runRecords _ _ _ _ _ _ _ _ (by omega : t ≤ N), paddedRecordValue, Sum.elim_inr]
    apply congrArg (fun f => (fixedHorizonRules N setting hs verdict hv).rule (t+1) (z,f))
    funext i
    cases i using Fin.lastCases <;> simp

/-- The pointwise terminal output is the specified test of all actual complete records, including N=0. -/
theorem fixedHorizon_terminalDecision (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) :
    terminalDecision (fixedHorizonRules N setting hs verdict hv) z x =
      verdict (fun i => (z i,x i.val)) := by
  rw [terminalDecision_eq_of_stopped _ z x N (fixedHorizon_everyPathCap _ _ _ _ _ z x),
    fixedHorizon_runAction _ _ _ _ _ _ _ _ le_rfl]
  simp [fixedHorizonRules, actionDecision]

/-- The stopping time is exactly N on all paths, rather than merely almost surely bounded by N. -/
theorem fixedHorizon_stoppingTime (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (z : Fin N → H) (x : ℕ → O) :
    stoppingTime (fixedHorizonRules N setting hs verdict hv) z x = (N : WithTop ℕ) := by
  have he : ∃ m, ¬runContinues (fixedHorizonRules N setting hs verdict hv) z x m :=
    ⟨N,fixedHorizon_everyPathCap _ _ _ _ _ z x⟩
  simp only [stoppingTime, dite_eq_left he]
  congr 1
  apply Nat.le_antisymm (Nat.find_min' he (fixedHorizon_everyPathCap _ _ _ _ _ z x))
  have h := Nat.find_spec he
  rw [fixedHorizon_runContinues_iff] at h
  omega

end LocalCertification.Protocol
