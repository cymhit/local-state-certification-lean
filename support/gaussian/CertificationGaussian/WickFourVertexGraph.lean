import CertificationGaussian.FourVertexOverlap
import CertificationGaussian.ComplexGaussianMatrixWick

noncomputable section
open Finset
open scoped BigOperators
namespace CertificationGaussian

/-- Count directed Wick edges by their original and permuted block labels. -/
def wickBlockCount (π : Equiv.Perm (Fin 4 × Fin 2)) (i j : Fin 4) : ℕ :=
  ∑ t : Fin 4 × Fin 2,if t.1=i ∧ (π t).1=j then 1 else 0

theorem wickBlockCount_row (π : Equiv.Perm (Fin 4 × Fin 2)) (i : Fin 4) :
    (∑ j,wickBlockCount π i j)=2 := by
  unfold wickBlockCount
  rw [Finset.sum_comm]
  have he (t : Fin 4 × Fin 2) :
      (∑ j : Fin 4,if t.1=i ∧ (π t).1=j then (1:ℕ) else 0)=if t.1=i then 1 else 0 := by
    by_cases ht : t.1=i <;> simp [ht]
  simp_rw [he]
  fin_cases i <;> decide

theorem wickBlockCount_column (π : Equiv.Perm (Fin 4 × Fin 2)) (j : Fin 4) :
    (∑ i,wickBlockCount π i j)=2 := by
  unfold wickBlockCount
  rw [Finset.sum_comm]
  have he (t : Fin 4 × Fin 2) :
      (∑ i : Fin 4,if t.1=i ∧ (π t).1=j then (1:ℕ) else 0)=if (π t).1=j then 1 else 0 := by
    by_cases ht : (π t).1=j <;> simp [ht]
  simp_rw [he]
  rw [Equiv.sum_comp π (fun t => if t.1=j then (1:ℕ) else 0)]
  fin_cases j <;> decide

theorem wickBlockCount_diagonal (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π ∈ fourBlockDerangements) (i : Fin 4) : wickBlockCount π i i=0 := by
  have h : ∀ t,(π t).1≠t.1 := (Finset.mem_filter.mp hπ).2
  unfold wickBlockCount
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : t.1=i
  · have hn : (π t).1≠i := by simpa only [ht] using h t
    simp [hn]
  · simp [ht]

/-- Eight actual Wick edges plus the actual four-cycle of the output trace. -/
def wickFourVertexGraph (π : Equiv.Perm (Fin 4 × Fin 2)) : FourVertexMultigraph where
  e01 := wickBlockCount π 0 1+wickBlockCount π 1 0+1
  e02 := wickBlockCount π 0 2+wickBlockCount π 2 0
  e03 := wickBlockCount π 0 3+wickBlockCount π 3 0+1
  e12 := wickBlockCount π 1 2+wickBlockCount π 2 1+1
  e13 := wickBlockCount π 1 3+wickBlockCount π 3 1
  e23 := wickBlockCount π 2 3+wickBlockCount π 3 2+1

theorem wickFourVertexGraph_cycle (π : Equiv.Perm (Fin 4 × Fin 2)) :
    (wickFourVertexGraph π).ContainsFourCycle := by
  simp only [FourVertexMultigraph.ContainsFourCycle,wickFourVertexGraph]
  omega

/-- Each block has exactly two outgoing and two incoming Wick edges, and two output edges. -/
theorem wickFourVertexGraph_regular (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π ∈ fourBlockDerangements) : (wickFourVertexGraph π).IsSixRegular := by
  simp only [FourVertexMultigraph.IsSixRegular,wickFourVertexGraph]
  refine ⟨?_,?_,?_,?_⟩
  · have hr := wickBlockCount_row π 0
    have hc := wickBlockCount_column π 0
    have hd := wickBlockCount_diagonal π hπ 0
    norm_num [Fin.sum_univ_succ] at hr hc
    omega
  · have hr := wickBlockCount_row π 1
    have hc := wickBlockCount_column π 1
    have hd := wickBlockCount_diagonal π hπ 1
    norm_num [Fin.sum_univ_succ] at hr hc
    omega
  · have hr := wickBlockCount_row π 2
    have hc := wickBlockCount_column π 2
    have hd := wickBlockCount_diagonal π hπ 2
    norm_num [Fin.sum_univ_succ] at hr hc
    omega
  · have hr := wickBlockCount_row π 3
    have hc := wickBlockCount_column π 3
    have hd := wickBlockCount_diagonal π hπ 3
    norm_num [Fin.sum_univ_succ] at hr hc
    omega

/-- Fiber grouping keeps the multiplicity of every one of the eight labelled Wick slots. -/
theorem wickBlockCount_product {M : Type*} [CommMonoid M]
    (π : Equiv.Perm (Fin 4 × Fin 2)) (f : Fin 4 → Fin 4 → M) :
    (∏ t : Fin 4 × Fin 2,f t.1 (π t).1) =
      ∏ i : Fin 4,∏ j : Fin 4,f i j^wickBlockCount π i j := by
  have h := Finset.prod_fiberwise' (Finset.univ : Finset (Fin 4 × Fin 2))
    (fun t => (t.1,(π t).1)) (fun p : Fin 4 × Fin 4 => f p.1 p.2)
  rw [← h,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_const]
  congr 1
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Prod.mk.injEq,wickBlockCount]


/-- The same twelve edges regroup into the six undirected multiplicities of the constructed graph. -/
theorem wickFourVertexGraph_product
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π ∈ fourBlockDerangements)
    (f : Fin 4 → Fin 4 → ℝ) (hs : ∀ i j,f i j=f j i) :
    (f 0 1*f 1 2*f 2 3*f 3 0)*(∏ t : Fin 4 × Fin 2,f t.1 (π t).1) =
      f 0 1^(wickFourVertexGraph π).e01 * f 0 2^(wickFourVertexGraph π).e02 *
      f 0 3^(wickFourVertexGraph π).e03 * f 1 2^(wickFourVertexGraph π).e12 *
      f 1 3^(wickFourVertexGraph π).e13 * f 2 3^(wickFourVertexGraph π).e23 := by
  rw [wickBlockCount_product]
  norm_num only [Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.reduceFinMk,Fin.reduceSucc,
    wickBlockCount_diagonal π hπ,pow_zero,mul_one,one_mul]
  simp only [hs 1 0,hs 2 0,hs 3 0,hs 2 1,hs 3 1,hs 3 2,
    wickFourVertexGraph,pow_add,pow_one]
  ring

end CertificationGaussian
