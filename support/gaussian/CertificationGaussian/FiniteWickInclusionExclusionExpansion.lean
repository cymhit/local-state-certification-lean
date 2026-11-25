import CertificationGaussian.FiniteWickInclusionExclusion

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

abbrev LocalWickEdge := Fin 2 × Fin 2

/-- The seven possible contractions in a two-bar, two-z block. -/
def localWickContractions : Finset (Finset LocalWickEdge) :=
  {∅, {(0,0)}, {(0,1)}, {(1,0)}, {(1,1)}, {(0,0),(1,1)}, {(0,1),(1,0)}}

/-- A selection of edges is a partial matching exactly when both endpoint maps are injective. -/
def LocalWickPartialMatching (s : Finset LocalWickEdge) : Prop :=
  (s.image Prod.fst).card = s.card ∧ (s.image Prod.snd).card = s.card

instance (s : Finset LocalWickEdge) : Decidable (LocalWickPartialMatching s) :=
  by unfold LocalWickPartialMatching; infer_instance

/-- Kernel-checked enumeration of the seven partial matchings, independent of coordinates. -/
theorem localWickContractions_mem_iff (s : Finset LocalWickEdge) :
    s ∈ localWickContractions ↔ LocalWickPartialMatching s := by
  revert s
  decide

/-- A single signed term of the actual normal-order expansion. -/
def localWickContractionPolynomial {I : Type*} [DecidableEq I]
    (i j : Fin 2 → I) (s : Finset LocalWickEdge) : MvPolynomial (Fin 2 × I) ℂ :=
  C ((-1 : ℂ) ^ s.card) * (∏ e ∈ s, gaussianDeltaPolynomial (i e.1) (j e.2)) *
    (∏ a ∈ (univ : Finset (Fin 2)) \ s.image Prod.fst, gaussianBarZPolynomial (i a)) *
    (∏ a ∈ (univ : Finset (Fin 2)) \ s.image Prod.snd, gaussianZPolynomial (j a))

/-- The finite contraction expansion is exactly the existing seven-term quartic. -/
theorem gaussianNormalQuartic_finite_expansion {I : Type*} [DecidableEq I]
    (i j : Fin 2 → I) :
    gaussianNormalQuartic (i 0) (i 1) (j 0) (j 1) =
      ∑ s ∈ localWickContractions, localWickContractionPolynomial i j s := by
  rw [gaussianNormalQuartic_expansion]
  simp only [localWickContractions]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  have h0 : ({(0 : Fin 2), 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  have h1 : ({(0 : Fin 2), 1} : Finset (Fin 2)) \ {1,0} = ∅ := by decide
  norm_num [localWickContractionPolynomial, Fin.univ_succ, h0, h1]
  ring

/-- Local internal edges of a fixed full matching; coordinates do not enter this set. -/
def localWickInternalEdges (π : Equiv.Perm FourWickPosition) (b : Fin 4) :
    Finset LocalWickEdge := univ.filter (fun e => π (b,e.1) = (b,e.2))

/-- Every subset of the local internal edges is one of the actual seven expansion terms. -/
theorem localWickInternalEdges_subset_term (π : Equiv.Perm FourWickPosition)
    (b : Fin 4) {s : Finset LocalWickEdge} (hs : s ⊆ localWickInternalEdges π b) :
    s ∈ localWickContractions := by
  rw [localWickContractions_mem_iff]
  constructor
  · apply Finset.card_image_of_injOn
    intro a ha c hc hac
    have hpa := (Finset.mem_filter.mp (hs ha)).2
    have hpc := (Finset.mem_filter.mp (hs hc)).2
    rw [hac] at hpa
    have he := congrArg (fun x : FourWickPosition => x.2) (hpa.symm.trans hpc)
    exact Prod.ext hac he
  · apply Finset.card_image_of_injOn
    intro a ha c hc hac
    have hpa := (Finset.mem_filter.mp (hs ha)).2
    have hpc := (Finset.mem_filter.mp (hs hc)).2
    have he : π (b,a.1) = π (b,c.1) := by rw [hpa, hpc, hac]
    have hf := congrArg (fun x : FourWickPosition => x.2) (π.injective he)
    exact Prod.ext hf hac

/-- At a fixed full matching, compatible normal-order terms are exactly edge subsets. -/
theorem localWick_expansion_fiber (π : Equiv.Perm FourWickPosition) (b : Fin 4) :
    localWickContractions.filter (fun s => s ⊆ localWickInternalEdges π b) =
      (localWickInternalEdges π b).powerset := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨localWickInternalEdges_subset_term π b h, h⟩⟩

/-- Thus the coefficient supplied by one actual normal-order block is its subset sum. -/
theorem localWick_expansion_coefficient (π : Equiv.Perm FourWickPosition) (b : Fin 4) :
    (∑ s ∈ localWickContractions,
      if s ⊆ localWickInternalEdges π b then (-1 : ℂ) ^ s.card else 0) =
      if localWickInternalEdges π b = ∅ then 1 else 0 := by
  rw [← Finset.sum_filter, localWick_expansion_fiber, finiteWick_subset_cancellation]

end CertificationGaussian
