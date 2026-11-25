/- One-point compactification of the weighted polynomial evaluation model. -/
import LocalCertification.Extremal.SupportCompression
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Filter Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Monomial coefficient model, with an independent limiting constant. -/
abbrev CoeffSpace (r : ℕ) := ℝ × (Fin (r + 1) → ℝ)

def coefficientPolynomial {r : ℕ} (c : CoeffSpace r) : ℝ[X] :=
  Polynomial.ofFn (r + 1) c.2

theorem coefficientPolynomial_degree {r : ℕ} (c : CoeffSpace r) :
    (coefficientPolynomial c).natDegree ≤ r := by
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) c.2)

theorem coefficientPolynomial_eval {r : ℕ} (c : CoeffSpace r) (w : ℝ) :
    (coefficientPolynomial c).eval w = ∑ j : Fin (r + 1), c.2 j * w ^ (j : ℕ) := by
  simp [coefficientPolynomial, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]

theorem polynomial_reconstruction {r : ℕ} (h : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ r) :
    coefficientPolynomial (r := r) (h, Polynomial.toFn (r + 1) p) = p := by
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hp)

theorem coefficients_reconstruction {r : ℕ} (c : CoeffSpace r) :
    (c.1, Polynomial.toFn (r + 1) (coefficientPolynomial c)) = c := by
  simp [coefficientPolynomial, Polynomial.toFn_comp_ofFn_eq_id]

theorem coeffSpace_finrank (r : ℕ) : Module.finrank ℝ (CoeffSpace r) = r + 2 := by
  simp only [CoeffSpace, Module.finrank_prod, Module.finrank_self, Module.finrank_pi, Fintype.card_fin]
  omega

/-- For every real base q, the natural power of q⁻¹ equals the real power of q with exponent −w. -/
theorem inverse_pow_eq_real_decay (q : ℝ) (w : ℕ) :
    (q⁻¹) ^ w = q ^ (-(w : ℝ)) := by
  simp [inv_pow]

theorem monomial_decay_tendsto (q : ℝ) (hq : 1 < q) (j : ℕ) :
    Tendsto (fun w : ℕ => (q⁻¹) ^ w * (w : ℝ) ^ j) atTop (𝓝 0) := by
  have h := tendsto_pow_const_mul_const_pow_of_lt_one j
    (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hq)))
    ((inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq)
  simpa only [mul_comm] using h

theorem polynomial_decay_tendsto (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    Tendsto (fun w : ℕ => (q⁻¹) ^ w * p.eval (w : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range (p.natDegree + 1))
    (fun j _ => (monomial_decay_tendsto q hq j).const_mul (p.coeff j))
  simpa [Polynomial.eval_eq_sum_range, Finset.mul_sum, mul_left_comm, mul_assoc] using h

theorem polynomial_real_decay_tendsto (q : ℝ) (hq : 1 < q) (p : ℝ[X]) :
    Tendsto (fun w : ℕ => q ^ (-(w : ℝ)) * p.eval (w : ℝ)) atTop (𝓝 0) := by
  simpa only [← inverse_pow_eq_real_decay] using polynomial_decay_tendsto q hq p

/-- Infinity is the limiting constant; finite label k means the node k+1. -/
def polynomialNode (q h : ℝ) (p : ℝ[X]) : OnePoint ℕ → ℝ :=
  fun x => x.elim h (fun k => h + (q⁻¹) ^ (k + 1) * p.eval ((k + 1 : ℕ) : ℝ))

@[simp] theorem polynomialNode_infty (q h : ℝ) (p : ℝ[X]) :
    polynomialNode q h p ∞ = h := rfl

@[simp] theorem polynomialNode_nat (q h : ℝ) (p : ℝ[X]) (k : ℕ) :
    polynomialNode q h p (k : OnePoint ℕ) =
      h + (q⁻¹) ^ (k + 1) * p.eval ((k + 1 : ℕ) : ℝ) := rfl

theorem polynomialNode_real_formula (q h : ℝ) (p : ℝ[X]) (k : ℕ) :
    polynomialNode q h p (k : OnePoint ℕ) =
      h + q ^ (-((k + 1 : ℕ) : ℝ)) * p.eval ((k + 1 : ℕ) : ℝ) := by
  rw [polynomialNode_nat, inverse_pow_eq_real_decay]

theorem polynomialNode_continuous (q : ℝ) (hq : 1 < q) (h : ℝ) (p : ℝ[X]) :
    Continuous (polynomialNode q h p) := by
  apply (OnePoint.continuous_iff_from_nat _).mpr
  simpa using tendsto_const_nhds.add
    ((polynomial_decay_tendsto q hq p).comp (tendsto_add_atTop_nat 1))

/-- Extrapolation is separately defined, and is never finite label zero. -/
def extrapolateZero (h : ℝ) (p : ℝ[X]) : ℝ := h + p.eval 0

theorem finite_label_zero (q h : ℝ) (p : ℝ[X]) :
    polynomialNode q h p (0 : ℕ) = h + q⁻¹ * p.eval 1 := by simp

theorem extrapolateZero_real_formula (q h : ℝ) (p : ℝ[X]) :
    extrapolateZero h p = h + q ^ (-(0 : ℝ)) * p.eval 0 := by
  simp [extrapolateZero]

def pairing {r : ℕ} (c : CoeffSpace r) : CoeffSpace r →ₗ[ℝ] ℝ where
  toFun v := c.1 * v.1 + ∑ j, c.2 j * v.2 j
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro j _; ring

def nodeMonomial (q : ℝ) (j : ℕ) : OnePoint ℕ → ℝ :=
  fun x => x.elim 0 (fun k => (q⁻¹) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ j)

theorem nodeMonomial_continuous (q : ℝ) (hq : 1 < q) (j : ℕ) :
    Continuous (nodeMonomial q j) := by
  apply (OnePoint.continuous_iff_from_nat _).mpr
  exact (monomial_decay_tendsto q hq j).comp (tendsto_add_atTop_nat 1)

def evaluationDictionary (q : ℝ) (r : ℕ) (x : OnePoint ℕ) : CoeffSpace r :=
  (1, fun j => nodeMonomial q j x)

@[simp] theorem evaluationDictionary_infty (q : ℝ) (r : ℕ) :
    evaluationDictionary q r ∞ = (1, 0) := rfl

@[simp] theorem evaluationDictionary_nat (q : ℝ) (r k : ℕ) :
    evaluationDictionary q r (k : OnePoint ℕ) =
      (1, fun j : Fin (r+1) => (q⁻¹) ^ (k+1) * ((k+1 : ℕ) : ℝ) ^ (j : ℕ)) := rfl

theorem evaluationDictionary_continuous (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Continuous (evaluationDictionary q r) :=
  continuous_const.prodMk (continuous_pi (fun j => nodeMonomial_continuous q hq j))

theorem pairing_dictionary {r : ℕ} (q : ℝ) (c : CoeffSpace r) (x : OnePoint ℕ) :
    pairing c (evaluationDictionary q r x) =
      polynomialNode q c.1 (coefficientPolynomial c) x := by
  induction x using OnePoint.rec with
  | infty => simp [pairing, evaluationDictionary, nodeMonomial]
  | coe k =>
    simp [pairing, evaluationDictionary, nodeMonomial, coefficientPolynomial_eval,
      Finset.mul_sum, mul_left_comm]

theorem model_covers_polynomial {r : ℕ} (q h : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ r) :
    ∃ c : CoeffSpace r, c.1 = h ∧ coefficientPolynomial c = p ∧
      (∀ x, pairing c (evaluationDictionary q r x) = polynomialNode q h p x) := by
  refine ⟨(h, Polynomial.toFn (r+1) p), rfl, polynomial_reconstruction h p hp, ?_⟩
  intro x
  rw [pairing_dictionary, polynomial_reconstruction h p hp]

def extrapolationDictionary (r : ℕ) : CoeffSpace r := (1, fun j => (0 : ℝ) ^ (j : ℕ))

theorem pairing_extrapolation {r : ℕ} (c : CoeffSpace r) :
    pairing c (extrapolationDictionary r) = extrapolateZero c.1 (coefficientPolynomial c) := by
  simp [pairing, extrapolationDictionary, extrapolateZero, coefficientPolynomial_eval]

/-- Signed evaluation atoms on the contact hyperplane of the actual node function. -/
def contactDictionary (q : ℝ) (r : ℕ) (c : CoeffSpace r) : Set (CoeffSpace r) :=
  {z | ∃ (x : OnePoint ℕ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
    z = ε • evaluationDictionary q r x ∧ pairing c z = 1}

theorem contactDictionary_compression (q : ℝ) (r : ℕ) (c : CoeffSpace r)
    {y : CoeffSpace r} (hy : y ∈ convexHull ℝ (contactDictionary q r c)) :
    ∃ (n : ℕ) (z : Fin n → CoeffSpace r) (a : Fin n → ℝ),
      (∀ i, z i ∈ contactDictionary q r c) ∧ (∀ i, 0 < a i) ∧
      (∑ i, a i = 1) ∧ (∑ i, a i • z i = y) ∧ LinearIndependent ℝ z ∧
      Function.Injective z ∧ n ≤ r + 2 := by
  obtain ⟨n, z, a, hz, ha, hs, he, hl, hi, hn⟩ :=
    positive_support_compression (pairing c) (contactDictionary q r c)
      (fun z hz => by obtain ⟨x, ε, hε, he, hc⟩ := hz; exact hc) hy
  exact ⟨n, z, a, hz, ha, hs, he, hl, hi, by rwa [coeffSpace_finrank] at hn⟩


/-- Distinct coefficient data cannot define the same actual OnePoint function. -/
theorem polynomialNode_pair_injective (q : ℝ) (hq : 1 < q) :
    Function.Injective (fun v : ℝ × ℝ[X] => polynomialNode q v.1 v.2) := by
  intro a b hab
  have hc : a.1 = b.1 := congrFun hab ∞
  have hp : a.2 = b.2 := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun n : ℕ => ((n+1 : ℕ) : ℝ)) := by
      intro i j hij
      exact Nat.add_right_cancel (Nat.cast_injective hij)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro t ⟨n, rfl⟩
    have hn := congrFun hab (n : OnePoint ℕ)
    simp only [polynomialNode_nat, hc] at hn
    exact mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hq))))
      (add_left_cancel hn)
  exact Prod.ext hc hp

theorem pairing_comm {r : ℕ} (c v : CoeffSpace r) : pairing c v = pairing v c := by
  simp [pairing, mul_comm]

/-- The image is exactly the functions represented by h+q^{-w}p(w), deg p≤r. -/
def nodeModelLinearMap (q : ℝ) (r : ℕ) :
    CoeffSpace r →ₗ[ℝ] (OnePoint ℕ → ℝ) :=
  LinearMap.pi (fun x => pairing (evaluationDictionary q r x))

theorem nodeModelLinearMap_apply (q : ℝ) (r : ℕ) (c : CoeffSpace r) :
    nodeModelLinearMap q r c = polynomialNode q c.1 (coefficientPolynomial c) := by
  funext x
  exact (pairing_comm _ _).trans (pairing_dictionary q c x)

theorem nodeModelLinearMap_injective (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Function.Injective (nodeModelLinearMap q r) := by
  intro a b hab
  rw [nodeModelLinearMap_apply, nodeModelLinearMap_apply] at hab
  have h : (a.1, coefficientPolynomial a) = (b.1, coefficientPolynomial b) := by
    apply polynomialNode_pair_injective q hq
    exact hab
  apply Prod.ext
  · exact congrArg (fun t : ℝ × ℝ[X] => t.1) h
  · exact Polynomial.injective_ofFn (r+1) (congrArg (fun t : ℝ × ℝ[X] => t.2) h)

theorem nodeFunctionSpace_finrank (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Module.finrank ℝ (LinearMap.range (nodeModelLinearMap q r)) = r + 2 := by
  rw [LinearMap.finrank_range_of_inj (nodeModelLinearMap_injective q hq r), coeffSpace_finrank]

theorem nodeFunctionSpace_mem_iff (q : ℝ) (r : ℕ) (f : OnePoint ℕ → ℝ) :
    f ∈ LinearMap.range (nodeModelLinearMap q r) ↔
      ∃ (h : ℝ) (p : ℝ[X]), p.natDegree ≤ r ∧ f = polynomialNode q h p := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.1, coefficientPolynomial c, coefficientPolynomial_degree c,
      nodeModelLinearMap_apply q r c⟩
  · rintro ⟨h, p, hp, rfl⟩
    refine ⟨(h, Polynomial.toFn (r+1) p), ?_⟩
    rw [nodeModelLinearMap_apply, polynomial_reconstruction h p hp]

theorem nodeFunctionSpace_continuous (q : ℝ) (hq : 1 < q) (r : ℕ)
    (f : LinearMap.range (nodeModelLinearMap q r)) : Continuous (f : OnePoint ℕ → ℝ) := by
  obtain ⟨h, p, hp, hf⟩ := (nodeFunctionSpace_mem_iff q r f).mp f.property
  rw [hf]
  exact polynomialNode_continuous q hq h p

/-- Actual distinct OnePoint nodes, signs, and positive weights after compression.
The convex-hull hypothesis is explicit: no extremizer existence is asserted here. -/
theorem contact_nodes_compression (q : ℝ) (r : ℕ) (c : CoeffSpace r)
    {y : CoeffSpace r} (hy : y ∈ convexHull ℝ (contactDictionary q r c)) :
    ∃ (n : ℕ) (x : Fin n → OnePoint ℕ) (ε a : Fin n → ℝ),
      Function.Injective x ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i, polynomialNode q c.1 (coefficientPolynomial c) (x i) = ε i) ∧
      (∀ i, 0 < a i) ∧ (∑ i, a i = 1) ∧
      (∑ i, a i • (ε i • evaluationDictionary q r (x i)) = y) ∧
      LinearIndependent ℝ (fun i => ε i • evaluationDictionary q r (x i)) ∧ n ≤ r + 2 := by
  classical
  obtain ⟨n, z, a, hz, ha, hs, he, hl, hi, hn⟩ := contactDictionary_compression q r c hy
  choose x ε hε hez hc using hz
  have hcontact (i : Fin n) : polynomialNode q c.1 (coefficientPolynomial c) (x i) = ε i := by
    have h := hc i
    rw [hez i, map_smul, smul_eq_mul, pairing_dictionary] at h
    rcases hε i with hsign | hsign <;> rw [hsign] at h ⊢ <;> linarith
  have hxi : Function.Injective x := by
    intro i j hij
    have heps : ε i = ε j := by rw [← hcontact i, ← hcontact j, hij]
    apply hi
    rw [hez i, hez j, hij, heps]
  refine ⟨n, x, ε, a, hxi, hε, hcontact, ha, hs, ?_, ?_, hn⟩
  · simpa only [hez] using he
  · have hzfun : z = fun i => ε i • evaluationDictionary q r (x i) := funext hez
    rw [← hzfun]
    exact hl

end LocalCertification.Extremal
