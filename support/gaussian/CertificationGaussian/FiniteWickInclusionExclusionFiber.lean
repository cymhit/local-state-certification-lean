import CertificationGaussian.FiniteWickInclusionExclusionAssembly

noncomputable section
open Finset
open scoped BigOperators
namespace CertificationGaussian

abbrev FourWickInternalSubset (π : Equiv.Perm FourWickPosition) :=
  {s : Finset FourWickPosition // s ⊆ fourWickInternalPositions π}

abbrev FourWickCompatibleChoice (π : Equiv.Perm FourWickPosition) :=
  {q : FourWickChoice // ∀ b, (q b).1 ⊆ localWickInternalEdges π b}

/-- Restrict the matching's local graph to the chosen labelled bar positions. -/
def fourWickSubsetChoice (π : Equiv.Perm FourWickPosition) (s : FourWickInternalSubset π) :
    FourWickCompatibleChoice π :=
  ⟨fun b => ⟨(localWickInternalEdges π b).filter (fun e => (b,e.1) ∈ s.1),
    localWickInternalEdges_subset_term π b (Finset.filter_subset _ _)⟩,
    fun _ => Finset.filter_subset _ _⟩

/-- Recover selected labelled positions from a compatible normal-order expansion choice. -/
def fourWickChoiceSubset (π : Equiv.Perm FourWickPosition) (q : FourWickCompatibleChoice π) :
    FourWickInternalSubset π :=
  ⟨univ.filter (fun a => (a.2,(π a).2) ∈ (q.1 a.1).1), by
    intro a ha
    have hm := (Finset.mem_filter.mp ha).2
    have he := (Finset.mem_filter.mp (q.2 a.1 hm)).2
    have hf := congrArg (fun x : FourWickPosition => x.1) he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩⟩

/-- A genuine bijection: finite normal-order choices compatible with a fixed complete matching
are exactly subsets of its internal labelled edges. -/
def fourWickExpansionFiberEquiv (π : Equiv.Perm FourWickPosition) :
    FourWickCompatibleChoice π ≃ FourWickInternalSubset π where
  toFun := fourWickChoiceSubset π
  invFun := fourWickSubsetChoice π
  left_inv q := by
    apply Subtype.ext
    funext b
    apply Subtype.ext
    ext e
    change (e ∈ (localWickInternalEdges π b).filter
      (fun e => (b,e.1) ∈ (fourWickChoiceSubset π q).1)) ↔ e ∈ (q.1 b).1
    simp only [Finset.mem_filter, fourWickChoiceSubset, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he,hq⟩
      have hp := (Finset.mem_filter.mp he).2
      simpa only [hp] using hq
    · intro he
      have hp := (Finset.mem_filter.mp (q.2 b he)).2
      exact ⟨q.2 b he, by simpa only [hp] using he⟩
  right_inv s := by
    apply Subtype.ext
    ext a
    simp only [fourWickChoiceSubset, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [fourWickSubsetChoice, Finset.mem_filter, localWickInternalEdges,
      Finset.mem_univ, true_and, Prod.mk.eta]
    constructor
    · exact fun h => h.2
    · intro ha
      have hi := (Finset.mem_filter.mp (s.2 ha)).2
      exact ⟨Prod.ext hi rfl,ha⟩

/-- For compatible choices, recovery is the selected domain, independent of coordinate labels. -/
theorem fourWickChoiceSubset_eq_domain (π : Equiv.Perm FourWickPosition)
    (q : FourWickCompatibleChoice π) :
    (fourWickChoiceSubset π q).1 = fourWickChoiceDomain q.1 := by
  ext a
  simp only [fourWickChoiceSubset, fourWickChoiceDomain, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨_,h,rfl⟩
  · intro h
    obtain ⟨e,he,hea⟩ := Finset.mem_image.mp h
    have hp := (Finset.mem_filter.mp (q.2 a.1 he)).2
    have hv : (π a).2 = e.2 := by
      have ha : a = (a.1,e.1) := Prod.ext rfl hea.symm
      rw [ha,hp]
    rw [hv, ← hea]
    exact he

/-- Selected domain decomposes into the four separate local domains. -/
def fourWickChoiceDomainEquiv (q : FourWickChoice) :
    (fourWickChoiceDomain q : Set FourWickPosition) ≃
      Σ b : Fin 4, ((q b).1.image Prod.fst : Set (Fin 2)) where
  toFun a := ⟨a.1.1,⟨a.1.2, (Finset.mem_filter.mp a.2).2⟩⟩
  invFun a := ⟨(a.1,a.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.2.2⟩⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

theorem fourWickChoiceDomain_card (q : FourWickChoice) :
    (fourWickChoiceDomain q).card = ∑ b, (q b).1.card := by
  have h := Fintype.card_congr (fourWickChoiceDomainEquiv q)
  simp only [Fintype.card_sigma] at h
  change Fintype.card ↥(fourWickChoiceDomain q) =
    ∑ b, Fintype.card ↥((q b).1.image Prod.fst) at h
  simp only [Fintype.card_coe] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro b _
  exact ((localWickContractions_mem_iff (q b).1).mp (q b).2).1

/-- The bijection preserves exactly the normal-order sign, including repeated coordinates. -/
theorem fourWickExpansionFiberEquiv_sign (π : Equiv.Perm FourWickPosition)
    (q : FourWickCompatibleChoice π) :
    fourWickChoiceSign q.1 = (-1 : ℂ) ^ (fourWickExpansionFiberEquiv π q).1.card := by
  change fourWickChoiceSign q.1 = (-1 : ℂ) ^ (fourWickChoiceSubset π q).1.card
  rw [fourWickChoiceSubset_eq_domain, fourWickChoiceDomain_card]
  exact Finset.prod_pow_eq_pow_sum _ _ _

end CertificationGaussian
