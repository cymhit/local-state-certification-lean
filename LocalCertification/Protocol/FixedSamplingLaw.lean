import LocalCertification.Protocol.CoordinateResampling
import LocalCertification.Protocol.FixedWordPrefix

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set LocalCertification.Information
open scoped BigOperators ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {H : Type u} {S : Type v} {O : Type w}
  [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace O]
  [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- The ordinary physical kernel is sampled only at requests made by the actual fixed-horizon raw rules. -/
def fixedSlotKernel (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (κ : Kernel S O) (m : ℕ) : Kernel (SlotHistory (Fin N → H) O m) (Option O) :=
  stopContinue (activePrefix (fixedHorizonRules N setting hs verdict hv) m)
    (activePrefix_measurable _ m)
    (κ.comap (prefixSetting (fixedHorizonRules N setting hs verdict hv) m) (prefixSetting_measurable _ m))

instance fixedSlotKernel_markov (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (κ : Kernel S O) [IsMarkovKernel κ] (m : ℕ) :
    IsMarkovKernel (fixedSlotKernel N setting hs verdict hv κ m) := by
  unfold fixedSlotKernel
  infer_instance

/-- On every simulated finite-word prefix before N, the next draw is the actual selected-setting kernel. -/
theorem fixedSlotKernel_fixedWordPrefix (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (κ : Kernel S O) (m : ℕ) (hm : m < N) (p : (Fin N → H) × (Fin N → O)) :
    fixedSlotKernel N setting hs verdict hv κ m (fixedWordPrefix N setting hs verdict hv m p) =
      (κ (setting (p.1 ⟨m,hm⟩))).map Option.some := by
  rw [fixedSlotKernel, stopContinue_apply, ite_eq_left (fixedWordPrefix_active _ _ _ _ _ m hm p),
    Kernel.comap_apply, fixedWordPrefix_setting _ _ _ _ _ m hm p]

/-- The literal conditional product sampling law has all actual finite executor marginals through N.
This identifies the already defined raw execution rather than postulating independent physical draws. -/
theorem fixedSamplingLaw_prefix (N : ℕ) (setting : H → S) (hs : Measurable setting)
    (verdict : (Fin N → H × O) → Fin 2) (hv : Measurable verdict)
    (κ : Kernel S O) [IsMarkovKernel κ]
    (ν : Measure (Fin N → H)) [IsProbabilityMeasure ν] (m : ℕ) (hm : m ≤ N) :
    (ν ⊗ₘ finiteProductKernel (κ.comap setting hs)).map (fixedWordPrefix N setting hs verdict hv m) =
      prefixLaw ν (fixedSlotKernel N setting hs verdict hv κ) m := by
  induction m with
  | zero =>
    apply Measure.ext_of_lintegral
    intro f hf
    erw [lintegral_map hf (fixedWordPrefix_measurable N setting hs verdict hv 0),
      Measure.lintegral_compProd (hf.comp (fixedWordPrefix_measurable N setting hs verdict hv 0))]
    change (∫⁻ z, ∫⁻ x, f (ULift.up z) ∂finiteProductKernel (κ.comap setting hs) z ∂ν) =
      ∫⁻ h, f h ∂ν.map ULift.up
    erw [lintegral_map hf measurable_up]
    simp only [lintegral_const, measure_univ, mul_one]
  | succ m ih =>
    have hlt : m < N := by omega
    change _ = prefixLaw ν (fixedSlotKernel N setting hs verdict hv κ) m ⊗ₘ
      fixedSlotKernel N setting hs verdict hv κ m
    rw [← ih (by omega)]
    apply Measure.ext_of_lintegral
    intro f hf
    change (∫⁻ a, f a ∂(ν ⊗ₘ finiteProductKernel (κ.comap setting hs)).map
      (fixedWordPrefix N setting hs verdict hv (m+1))) =
      ∫⁻ a : SlotHistory (Fin N → H) O m × Option O, f a
        ∂((ν ⊗ₘ finiteProductKernel (κ.comap setting hs)).map (fixedWordPrefix N setting hs verdict hv m)) ⊗ₘ
          fixedSlotKernel N setting hs verdict hv κ m
    erw [lintegral_map hf (fixedWordPrefix_measurable N setting hs verdict hv (m+1)),
      Measure.lintegral_compProd (show Measurable (fun a : SlotHistory (Fin N → H) O m × Option O => f a) from hf),
      lintegral_map (hf.lintegral_kernel_prod_right') (fixedWordPrefix_measurable N setting hs verdict hv m),
      Measure.lintegral_compProd (hf.comp (fixedWordPrefix_measurable N setting hs verdict hv (m+1))),
      Measure.lintegral_compProd ((hf.lintegral_kernel_prod_right').comp (fixedWordPrefix_measurable N setting hs verdict hv m))]
    apply lintegral_congr
    intro z
    change (∫⁻ x, f (fixedWordPrefix N setting hs verdict hv (m+1) (z,x))
      ∂Measure.pi (fun i : Fin N => κ (setting (z i)))) = _
    calc
      _ = ∫⁻ x, ∫⁻ o, f (fixedWordPrefix N setting hs verdict hv (m+1)
          (z,Function.update x ⟨m,hlt⟩ o)) ∂κ (setting (z ⟨m,hlt⟩))
          ∂Measure.pi (fun i : Fin N => κ (setting (z i))) :=
        lintegral_pi_coordinate_resample (fun i : Fin N => κ (setting (z i))) ⟨m,hlt⟩
          (fun x => f (fixedWordPrefix N setting hs verdict hv (m+1) (z,x)))
          (hf.comp ((fixedWordPrefix_measurable N setting hs verdict hv (m+1)).comp
            (measurable_const.prodMk measurable_id)))
      _ = ∫⁻ x, ∫⁻ o, f (fixedWordPrefix N setting hs verdict hv m (z,x), some o)
          ∂κ (setting (z ⟨m,hlt⟩)) ∂Measure.pi (fun i : Fin N => κ (setting (z i))) := by
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro o
        apply congrArg f
        rw [fixedWordPrefix_succ N setting hs verdict hv m hlt]
        change (fixedWordPrefix N setting hs verdict hv m (z,Function.update x ⟨m,hlt⟩ o),
          some (Function.update x ⟨m,hlt⟩ o ⟨m,hlt⟩)) = _
        rw [fixedWordPrefix_update N setting hs verdict hv m ⟨m,hlt⟩ le_rfl (z,x) o,
          Function.update_self]
      _ = _ := by
        apply lintegral_congr
        intro x
        change _ = ∫⁻ b, f (fixedWordPrefix N setting hs verdict hv m (z,x),b)
          ∂fixedSlotKernel N setting hs verdict hv κ m (fixedWordPrefix N setting hs verdict hv m (z,x))
        erw [fixedSlotKernel_fixedWordPrefix N setting hs verdict hv κ m hlt (z,x),
          lintegral_map (show Measurable (fun b : Option O => f (fixedWordPrefix N setting hs verdict hv m (z,x),b)) from
            hf.comp measurable_prodMk_left) (measurable_of_countable Option.some)]

end LocalCertification.Protocol
