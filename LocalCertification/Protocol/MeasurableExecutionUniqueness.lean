import LocalCertification.Protocol.MeasurableExecution

/-! Probability laws of the actual seed and infinite record stream are
determined by their complete finite prefixes.  The proof uses generating
measurable cylinders on the genuine trajectory space.  No finiteness,
nonemptiness, or standard Borel assumption on either space is needed. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Preorder
  LocalCertification.Information.KernelHistory
noncomputable section

namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z Ω : Type u} [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Recover the original seed from a complete recursive prefix. -/
def prefixSeed : (n : ℕ) → FullHistory Z Ω n → Z
  | 0, z => z
  | n+1, h => prefixSeed n h.1

theorem prefixSeed_measurable (n : ℕ) : Measurable (prefixSeed (Z := Z) (Ω := Ω) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

/-- Recover any one of the recorded outcomes, including its original label. -/
def prefixRecord : (n : ℕ) → FullHistory Z Ω n → Fin n → Ω
  | 0, _, i => Fin.elim0 i
  | n+1, h, i => Fin.lastCases h.2 (fun k => prefixRecord n h.1 k) i

theorem prefixRecord_measurable (n : ℕ) (i : Fin n) :
    Measurable (fun h : FullHistory Z Ω n => prefixRecord n h i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    change Measurable (fun h : FullHistory Z Ω n × Ω =>
      Fin.lastCases (motive := fun _ : Fin (n+1) => Ω) h.2 (fun k => prefixRecord n h.1 k) i)
    cases i using Fin.lastCases with
    | last => simpa only [prefixRecord, Fin.lastCases_last] using
        (measurable_snd : Measurable (fun h : FullHistory Z Ω n × Ω => h.2))
    | cast i => simpa only [prefixRecord, Fin.lastCases_castSucc, Function.comp_def] using
        (ih i).comp measurable_fst

omit [MeasurableSpace Z] [MeasurableSpace Ω] in
theorem prefixSeed_rawPrefix (n : ℕ) (p : Sample Z Ω) :
    prefixSeed n (rawPrefix n p) = p.1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

omit [MeasurableSpace Z] [MeasurableSpace Ω] in
theorem prefixRecord_rawPrefix (n : ℕ) (p : Sample Z Ω) (i : Fin n) :
    prefixRecord n (rawPrefix n p) i = p.2 i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    change Fin.lastCases (p.2 n) (fun k => prefixRecord n (rawPrefix n p) k) i = p.2 i
    cases i using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, Fin.val_last]
    | cast i => simpa only [Fin.lastCases_castSucc, Fin.val_castSucc] using ih i

/-- The finite heterogeneous trajectory coordinates are measurable functions
of the seed and all recorded outcomes in the recursive prefix. -/
def encodePrefix (n : ℕ) (h : FullHistory Z Ω n) : (i : Finset.Iic n) → Coord Z Ω i
  | ⟨0, _⟩ => prefixSeed n h
  | ⟨k+1, hk⟩ => prefixRecord n h ⟨k, Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩

theorem encodePrefix_measurable (n : ℕ) : Measurable (encodePrefix (Z := Z) (Ω := Ω) n) := by
  apply measurable_pi_iff.mpr
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact prefixSeed_measurable n
  | succ k => exact prefixRecord_measurable n ⟨k, Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩

omit [MeasurableSpace Z] [MeasurableSpace Ω] in
theorem encodePrefix_rawPrefix (n : ℕ) (p : Sample Z Ω) :
    encodePrefix n (rawPrefix n p) = frestrictLe n (pack p) := by
  funext i
  rcases i with ⟨k, hk⟩
  cases k with
  | zero => exact prefixSeed_rawPrefix n p
  | succ k => exact prefixRecord_rawPrefix n p ⟨k, Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩

/-- Complete finite prefix laws determine the actual probability law on
the seed and infinite record stream, for arbitrary measurable spaces. -/
theorem law_ext_prefix (μ ν : Measure (Sample Z Ω)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, μ.map (rawPrefix n) = ν.map (rawPrefix n)) : μ = ν := by
  have hm : ∀ n : ℕ, (μ.map pack).map (frestrictLe n) = (ν.map pack).map (frestrictLe n) := by
    intro n
    have hc (ξ : Measure (Sample Z Ω)) :
        (ξ.map pack).map (frestrictLe n) = (ξ.map (rawPrefix n)).map (encodePrefix n) := by
      rw [Measure.map_map (measurable_frestrictLe n) pack_measurable,
        Measure.map_map (encodePrefix_measurable n) (rawPrefix_measurable n)]
      apply congrArg (Measure.map · ξ)
      funext p
      exact (encodePrefix_rawPrefix n p).symm
    rw [hc μ, hc ν, h n]
  have hprob (ξ : Measure (Sample Z Ω)) [IsProbabilityMeasure ξ] :
      IsProbabilityMeasure (ξ.map pack) := by
    constructor
    rw [Measure.map_apply pack_measurable MeasurableSet.univ]
    simp
  let := hprob μ
  let := hprob ν
  have he : μ.map pack = ν.map pack := by
    apply ext_of_generate_finite (measurableCylinders (Coord Z Ω))
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    · intro s hs
      rw [measurableCylinders_nat] at hs
      obtain ⟨n, hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨A, hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨hA, hs⟩ := Set.mem_iUnion.mp hs
      have heq : s = cylinder (Finset.Iic n) A := Set.mem_singleton_iff.mp hs
      subst s
      have hp := congrArg (fun ξ => ξ A) (hm n)
      rw [Measure.map_apply (measurable_frestrictLe n) hA,
        Measure.map_apply (measurable_frestrictLe n) hA] at hp
      exact hp
    · simp only [measure_univ]
  exact MeasurableEquiv.map_measurableEquiv_injective (sampleEquiv (Z := Z) (Ω := Ω)).symm he

/-- The actual Ionescu--Tulcea execution is the unique probability law with
the specified seeded, history-dependent iterated composition-product marginals. -/
theorem executionLaw_unique (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)]
    (law : Measure (Sample Z Ω)) [IsProbabilityMeasure law]
    (h : ∀ n, law.map (rawPrefix n) = prefixLaw seed κ n) : law = executionLaw seed κ := by
  apply law_ext_prefix law (executionLaw seed κ)
  intro n
  rw [h n, executionLaw_prefix seed κ n]

end LocalCertification.Protocol.MeasurableExecution
