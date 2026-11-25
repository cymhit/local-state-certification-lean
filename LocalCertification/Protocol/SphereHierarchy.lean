import LocalCertification.Protocol.BudgetHierarchy
import LocalCertification.Quantum.CompactTargetTransfer

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

def sphereHierarchyFailure (r : ℕ) (C c : ℝ) (n : ℕ) : ℝ :=
  hierarchyFailure r C c n+1/((n:ℝ)+1)

theorem sphereHierarchyFailure_tendsto (r : ℕ) (C c : ℝ) (hc : 0<c) :
    Tendsto (sphereHierarchyFailure r C c) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => hierarchyFailure r C c n+1/((n:ℝ)+1)) atTop (nhds 0)
  simpa only [add_zero] using (hierarchyFailure_tendsto r C c hc).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))

/-- The common-event hierarchy holds on actual compact subsets of the canonical unit sphere.
The compact-image transfer removes all dependence on a choice of Haar representative. -/
theorem qudit_budget_sphere_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C Cbad cdecay : ℝ,0<c ∧ 0<C ∧ 0<Cbad ∧ 0<cdecay ∧
      Tendsto (sphereHierarchyFailure r Cbad cdecay) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),IsCompact good ∧
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ≤
          ENNReal.ofReal (sphereHierarchyFailure r Cbad cdecay n) ∧
        ∀ ψ∈good,∀ δ : ℝ,0<δ → δ≤1/3 →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  classical
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨c,C,Cbad,cdecay,hc,hC,hCbad,hdecay,_ht,hN⟩ := qudit_budget_hierarchy d hd a b hb hab ha
  refine ⟨c,C,Cbad,cdecay,hc,hC,hCbad,hdecay,sphereHierarchyFailure_tendsto r Cbad cdecay hdecay,?_⟩
  filter_upwards [hN] with n hn
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨ψ₀⟩ := NormedSpace.sphere_nonempty_rclike (E:=EuclideanSpace ℂ (QuditIndex d n)) ℂ
    (show (0:ℝ)≤1 by norm_num)
  obtain ⟨bad,hm,hprob,hbound⟩ := hn ψ₀
  obtain ⟨good,hcompact,hgood,hfiber⟩ := haar_good_compact_targets (QuditIndex d n) ψ₀ bad hm
    (1/((n:ℝ)+1)) (by positivity)
  refine ⟨good,hcompact,?_,?_⟩
  · apply hgood.trans
    calc
      complexUnitaryHaar (QuditIndex d n) bad+ENNReal.ofReal (1/((n:ℝ)+1))≤
          ENNReal.ofReal (hierarchyFailure r Cbad cdecay n)+ENNReal.ofReal (1/((n:ℝ)+1)) :=
        add_le_add hprob le_rfl
      _=ENNReal.ofReal (sphereHierarchyFailure r Cbad cdecay n) := by
        rw [sphereHierarchyFailure,ENNReal.ofReal_add (hierarchyFailure_nonneg r Cbad cdecay hCbad.le n) (by positivity)]
  · intro ψ hψ δ hδ hthird
    obtain ⟨U,hU,hUψ⟩ := hfiber ψ hψ
    have h := hbound U hU δ hδ hthird
    simpa only [haarPureVector,hUψ] using h

/-- Canonical Haar-typical pure targets have the exact critical polynomial order for
both original budgets, uniformly over every error level 0<delta<=1/3. The target sets are genuinely
compact and their canonical sphere probabilities tend to one. -/
theorem qudit_theorem_one_one (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/3 →
        ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
        expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  classical
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨c,C,Cbad,cdecay,hc,hC,_hCbad,_hdecay,ht,hN⟩ :=
    qudit_budget_sphere_hierarchy d hd a b hb hab ha
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    IsCompact s ∧ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ≤
      ENNReal.ofReal (sphereHierarchyFailure r Cbad cdecay n) ∧
    ∀ ψ∈s,∀ δ : ℝ,0<δ → δ≤1/3 →
      ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
      expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
      ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
        ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))
  let good (n : ℕ) : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
    if h : ∃ s,P n s then h.choose else ∅
  have hcompact (n : ℕ) : IsCompact (good n) := by
    by_cases h : ∃ s,P n s
    · exact (by simpa only [good,dite_eq_left h] using h.choose_spec.1)
    · simpa only [good,dite_eq_right h] using isCompact_empty
  have hP : ∀ᶠ n : ℕ in atTop,P n (good n) := by
    filter_upwards [hN] with n hn
    have h : ∃ s,P n s := hn
    simpa only [good,dite_eq_left h] using h.choose_spec
  have hzero : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ)
      atTop (nhds 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop,
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤
          ENNReal.ofReal (sphereHierarchyFailure r Cbad cdecay n) := hP.mono (fun _ hn => hn.2.1)
    have hlim : Tendsto (fun n => ENNReal.ofReal (sphereHierarchyFailure r Cbad cdecay n)) atTop (nhds 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero,r] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun _ => bot_le)) hbound
  have hone : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) := by
    have h := (ENNReal.continuous_sub_left (show (1:ℝ≥0∞)≠∞ by simp)).continuousAt.tendsto.comp hzero
    have heq (n : ℕ) : 1-canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ=
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n) := by
      let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
      simpa only [compl_compl] using (prob_compl_eq_one_sub (hcompact n).isClosed.measurableSet.compl).symm
    simpa only [Function.comp_def,tsub_zero,heq] using h
  exact ⟨c,C,hc,hC,good,hcompact,hone,hP.mono (fun _ hn => hn.2.2)⟩

end LocalCertification.Protocol
