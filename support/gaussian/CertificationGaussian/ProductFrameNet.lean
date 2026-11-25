import CertificationGaussian.PhysicalProductFrame

/-! # One finite net for all product measurement frames

Centers are tuples of actual canonical frames, retaining their probability
witnesses. The same net covers the full product of compact closures. The mesh
is chosen before a measurement and gives the dimension-scaled error v/n.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

omit [Fintype S] [DecidableEq S] in
theorem canonicalRankOneFrame_closure_norm_le (T : ComplexMatrixFrameSpace I)
    (hT : T ∈ closure (canonicalRankOneFrames (I := I))) :
    ‖T‖ ≤ (Fintype.card I : ℝ)⁻¹ := by
  have hsub : canonicalRankOneFrames (I := I) ⊆
      {T : ComplexMatrixFrameSpace I | ‖T‖ ≤ (Fintype.card I : ℝ)⁻¹} := by
    intro T hT
    exact canonicalRankOneFrames_norm_le ⟨T,hT⟩
  exact closure_minimal hsub (isClosed_le continuous_norm continuous_const) hT

theorem canonicalProductFrame_exists_net (ε : ℝ) (hε : 0 < ε) :
    ∃ net : Finset (S → canonicalRankOneFrames (I := I)),
      (∀ T : S → ComplexMatrixFrameSpace I,
        (∀ s, T s ∈ closure (canonicalRankOneFrames (I := I))) →
        ∃ U ∈ net, ∀ s, ‖T s-(U s).val‖ ≤ ε) ∧
      (net.card : ℝ) ≤ (1+2*(Fintype.card I : ℝ)⁻¹/ε)^(2*(Fintype.card I)^4*(Fintype.card S)) := by
  classical
  obtain ⟨localNet, hcover, hcard⟩ := canonicalRankOneFrames_exists_closure_net (I := I) ε hε
  let net := Fintype.piFinset (fun _ : S => localNet)
  refine ⟨net, ?_, ?_⟩
  · intro T hT
    choose U hU hd using fun s => hcover (T s) (hT s)
    exact ⟨U, Fintype.mem_piFinset.mpr hU, hd⟩
  · calc
      (net.card : ℝ) = (localNet.card : ℝ)^(Fintype.card S) := by
        simp only [net, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Nat.cast_pow]
      _ ≤ ((1+2*(Fintype.card I : ℝ)⁻¹/ε)^(2*(Fintype.card I)^4))^(Fintype.card S) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
      _ = _ := by rw [← pow_mul]

theorem signedProductMatrixFrame_exists_net (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ net : Finset (S → canonicalRankOneFrames (I := I)),
      (∀ T : S → ComplexMatrixFrameSpace I,
        (∀ s, T s ∈ closure (canonicalRankOneFrames (I := I))) →
        ∃ U ∈ net, ((Fintype.card I : ℝ)^(Fintype.card S))^2 *
          ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ (fun s => (U s).val)‖ ≤
            (Fintype.card I : ℝ)*(Fintype.card I : ℝ)^(Fintype.card S)*
              (∑ k ∈ J, |θ k|)^2*(Fintype.card S : ℝ)*ε) ∧
      (net.card : ℝ) ≤ (1+2*(Fintype.card I : ℝ)⁻¹/ε)^(2*(Fintype.card I)^4*(Fintype.card S)) := by
  obtain ⟨net, hcover, hcard⟩ := canonicalProductFrame_exists_net (S := S) (I := I) ε hε
  refine ⟨net, ?_, hcard⟩
  intro T hT
  obtain ⟨U,hU,hclose⟩ := hcover T hT
  exact ⟨U,hU,signedProductMatrixFrame_scaled_distance_le hd J θ T (fun s => (U s).val) hε.le
    (fun s => canonicalRankOneFrame_closure_norm_le (T s) (hT s))
    (fun s => canonicalRankOneFrames_norm_le (U s)) hclose⟩

/-- The actual finite net at the paper's uniform v/n sphere-energy scale. -/
theorem signedProductMatrixFrame_exists_scaled_net (hd : 2 ≤ Fintype.card I)
    (hn : 0 < Fintype.card S) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hL : 0 < ∑ k ∈ J, |θ k|) (v : ℝ) (hv : 0 < v) :
    ∃ net : Finset (S → canonicalRankOneFrames (I := I)),
      (∀ T : S → ComplexMatrixFrameSpace I,
        (∀ s, T s ∈ closure (canonicalRankOneFrames (I := I))) →
        ∃ U ∈ net, ((Fintype.card I : ℝ)^(Fintype.card S))^2 *
          ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ (fun s => (U s).val)‖ ≤
            v/(Fintype.card S : ℝ)) ∧
      (net.card : ℝ) ≤
        (1+2*(Fintype.card I : ℝ)^(Fintype.card S)*(∑ k ∈ J, |θ k|)^2*
          (Fintype.card S : ℝ)^2/v)^(2*(Fintype.card I)^4*(Fintype.card S)) := by
  let d : ℝ := Fintype.card I
  let n : ℝ := Fintype.card S
  let D : ℝ := d^(Fintype.card S)
  let L : ℝ := ∑ k ∈ J, |θ k|
  let ε := v/(d*D*L^2*n^2)
  have hdpos : 0 < d := by dsimp [d]; exact_mod_cast (by omega : 0 < Fintype.card I)
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hDpos : 0 < D := pow_pos hdpos _
  have hLpos : 0 < L := hL
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : d*D*L^2*n*ε = v/n := by
    dsimp [ε]
    field_simp
  have hcardscale : 1+2*d⁻¹/ε = 1+2*D*L^2*n^2/v := by
    dsimp [ε]
    field_simp
  obtain ⟨net,hcover,hcard⟩ := signedProductMatrixFrame_exists_net (S := S) hd J θ ε hε
  refine ⟨net, ?_, ?_⟩
  · intro T hT
    obtain ⟨U,hU,he⟩ := hcover T hT
    refine ⟨U,hU,?_⟩
    change D^2 * ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ (fun s => (U s).val)‖ ≤ v/n
    change D^2 * ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ (fun s => (U s).val)‖ ≤
      d*D*L^2*n*ε at he
    rwa [hscale] at he
  · change (net.card : ℝ) ≤ (1+2*d⁻¹/ε)^(2*(Fintype.card I)^4*(Fintype.card S)) at hcard
    rw [hcardscale] at hcard
    exact hcard

/-- A fixed family of real HS operators containing every actual product refinement. -/
def signedProductFrameFamily (J : Finset ℕ) (θ : ℕ → ℝ) :
    Set (EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℝ] EuclideanSpace ℂ ((S → I) × (S → I))) :=
  {T | ∃ V : S → ComplexMatrixFrameSpace I,
    (∀ s, V s ∈ closure (canonicalRankOneFrames (I := I))) ∧
    T = (signedProductMatrixFrame J θ V).restrictScalars ℝ}

/-- The finite real-operator net needed by the common Gaussian/sphere transfer.
Every center still has an actual canonical probability-ensemble witness. -/
theorem signedProductFrameFamily_exists_scaled_net (hd : 2 ≤ Fintype.card I)
    (hn : 0 < Fintype.card S) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hL : 0 < ∑ k ∈ J, |θ k|) (v : ℝ) (hv : 0 < v) :
    ∃ net : Finset (EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℝ]
      EuclideanSpace ℂ ((S → I) × (S → I))),
      (∀ W ∈ net, ∃ U : S → canonicalRankOneFrames (I := I),
        W = (signedProductMatrixFrame J θ (fun s => (U s).val)).restrictScalars ℝ) ∧
      (∀ T ∈ signedProductFrameFamily (S := S) (I := I) J θ,
        ∃ W ∈ net, ((Fintype.card I : ℝ)^(Fintype.card S))^2 * ‖T-W‖ ≤ v/(Fintype.card S : ℝ)) ∧
      (net.card : ℝ) ≤
        (1+2*(Fintype.card I : ℝ)^(Fintype.card S)*(∑ k ∈ J, |θ k|)^2*
          (Fintype.card S : ℝ)^2/v)^(2*(Fintype.card I)^4*(Fintype.card S)) := by
  classical
  obtain ⟨s,hcover,hcard⟩ := signedProductMatrixFrame_exists_scaled_net (S := S) hd hn J θ hL v hv
  let f := fun U : S → canonicalRankOneFrames (I := I) =>
    (signedProductMatrixFrame J θ (fun s => (U s).val)).restrictScalars ℝ
  refine ⟨s.image f, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hW
    exact ⟨U,hU.symm⟩
  · rintro T ⟨V,hV,rfl⟩
    obtain ⟨U,hU,hdist⟩ := hcover V hV
    refine ⟨f U, Finset.mem_image.mpr ⟨U,hU,rfl⟩, ?_⟩
    have he : ‖(signedProductMatrixFrame J θ V).restrictScalars ℝ-f U‖ =
        ‖signedProductMatrixFrame J θ V-signedProductMatrixFrame J θ (fun s => (U s).val)‖ := by
      change ‖(signedProductMatrixFrame J θ V-
        signedProductMatrixFrame J θ (fun s => (U s).val)).restrictScalars ℝ‖ = _
      exact ContinuousLinearMap.norm_restrictScalars _
    rwa [he]
  · exact (Nat.cast_le.mpr (Finset.card_image_le : (s.image f).card ≤ s.card)).trans hcard

end CertificationGaussian
