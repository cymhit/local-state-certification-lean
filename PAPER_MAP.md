# Paper-to-Lean map

The [correspondence table](docs/paper-map.tsv) indexes the three main results of *Sharp Transitions of Copy Complexity in Local Certification of Typical Pure States*, the statements and equations in the Supplemental Material, and the eleven exact qubit certificates in Table S1.

### Reading a correspondence row

Each row gives a stable result identifier or TeX label, a section, and the scope of the correspondence. The Lean declarations and repository-relative paths are paired in order. Selected direct dependencies have the form `value|declaration|dependency` or `type|declaration|dependency`. The former occurs in a definition or proof term and the latter in a statement. To read the complete elaborated types after the [full build](README.md), run

~~~sh
python3 -B scripts/inspect_paper_row.py --build ../certification-full --dependencies ../certification-dependencies/state.json T1 C2 T3
~~~

The command checks the source and module hashes against the full-build receipt, imports the compiled owners and prints one JSON record per distinct declaration. Each record includes the elaborated type with implicit arguments, universe parameters, direct type references and direct value references. Replace the three IDs with, for example, `S19 Eq.S94 WIENER TableS1.r4`. A row classified as outside formal scope has no Lean target. The full verifier also runs the formal axiom and proof-route checks.

`LocalCertification/Paper.lean` provides stable semantic exports. `LocalCertification/LegacyPaper.lean` contains the separate product-basis interface and its specialized checks. The general product-POVM lower bounds use the measurable-POVM and common-frame proof described below.

## Main results and scope

All names in the second column belong to `LocalCertification.Paper`. The detailed map gives fully qualified implementation declarations.

| Paper statement | Public export | Implementation endpoint |
| --- | --- | --- |
| Theorem 1, fixed confidence range | `tolerance_hierarchy`, `theorem_1` | `ProductBudget.product_budget_same_event_confidence_hierarchy` |
| Exact testing-scale bounds | `tolerance_testing_bounds` | `ProductBudget.product_budget_sphere_hierarchy` |
| Actual unitary-Haar targets | `tolerance_haar_bounds` | `ProductBudget.product_budget_haar_hierarchy` |
| Corollary 2, simultaneous threshold and confidence uniformity | `corollary_2` | `MeasurableExecution.qudit_nearCritical_product_neighborhood_confidence` |
| Open neighborhood at a fixed error probability | `near_critical_neighborhood` | `MeasurableExecution.qudit_nearCritical_product_neighborhood` |
| Closed two-threshold window, exact testing factor | `near_critical_window` | `MeasurableExecution.qudit_nearCritical_product_hierarchy_uniform` |
| Same window, logarithmic confidence bounds | `near_critical_window_confidence` | `MeasurableExecution.qudit_nearCritical_product_confidence_uniform` |
| Fixed-baseline specialization | `near_critical_testing_bounds`, `near_critical_transition` | `MeasurableExecution.qudit_nearCritical_product_hierarchy`, `qudit_nearCritical_product_confidence_hierarchy` |
| Theorem 3 | `theorem_3` | `Manuscript.physical_sharp_order_and_inversion` |
| Theorem 3, repeated-node Wiener proof | `theorem_3_wiener` | `Manuscript.physical_wiener_sharp_order_and_inversion` |
| S23 fixed partition hierarchy | `fixed_block_hierarchy` | `FixedBlock.fixedBlock_budget_same_event_confidence_hierarchy` |
| S23 exact bounds and strict threshold | `fixed_block_testing_bounds`, `fixed_block_threshold` | `FixedBlock.fixedBlock_budget_sphere_hierarchy`, `fixedBlock_budget_same_event_criterion` |

For **Theorem 1**, fix \(d\ge2\), \(0<b<a\le1\), \(g=(a-b)/(1-b)\), and the strict critical degree \(r=\min\{s:\gamma_s(d)<g\}\). A single compact target family, positive exponential failure rate, upper constant and dimension cutoff work before choosing the confidence cutoff. The exact lower scale is \(n^r L_\delta\), where `testingThreshold` defines \(L_\delta\). The logarithmic lower constant may depend on a fixed \(0<\delta_*<1/2\). Expected budgets take values in the extended nonnegative reals, and maximum budgets in the extended naturals. Their definitions retain infinite costs and do not assume the existence of a finite-cost valid protocol.

For **Corollary 2**, the convention is \(g=\gamma_j(d)+\varepsilon\), on a fixed closed window \(-\eta\le\varepsilon\le\eta\). The crossover scale is

\[
\frac{n^{j+1}}{1+n(\max\{\varepsilon,0\})^2}.
\]

The window is smaller than half the minimum adjacent critical gap, with preceding value \(1\) at \(j=0\). The upper and lower constructions on this closed window prove (S105) with a common compact typical family and size cutoff. For a center with normalized gap \(\gamma_j(d)\), take an open interval in the running \(b\) and pull the open \(\varepsilon\)-interval back under the normalized gap. The resulting open set \(U\) contains the center and lies within \(0<b<a<1\).

The public theorem chooses \(U\), an upper constant, the typical family and a common cutoff before \(\delta_\star\). For each \(0<\delta_\star<1/2\) it supplies a positive lower constant. The bounds hold for every size above the cutoff, every target in that same family, both running thresholds in \(U\), and every \(0<\delta\le\delta_\star\). The exact testing factor \(L_\delta\) is uniformly comparable to \(\log(1/\delta)\) on this cutoff range by (S104). Write \(S\) for the displayed fraction above. For positive excess, put \(R=\min\{n^j/\varepsilon^2,n^{j+1}\}\). For nonpositive excess put \(R=n^{j+1}\). The comparison \(S\le R\le 2S\) converts the closed bounds into (8), including the crossover at \(\varepsilon=n^{-1/2}\). The upper bound supplies a feasible integer cap. At \(j=0\) the positive-side lower construction uses the \(H_0\)/target-state mixture and its zero-radius kernel. At positive degrees it mixes two adjacent calibrated pairs.

For **Theorem 3**, both numbered exports take a physical integer \(d\ge2\). They specialize `Manuscript.sharp_order_and_inversion` and `Manuscript.wiener_sharp_order_and_inversion` for a fixed real \(d>0\), with decay base \(q=d+1\). The sharp two-sided bounds apply at integer degree at least two. The inversion is one-sided for positive \(g\to0\) at fixed \(d\). A strict crossing is the first degree with \(\gamma_r(d)<g\). Equality at a step point advances the degree by one.

For **S23**, each prescribed partition into blocks of size \(k\ge1\) is fixed across all copies. Arbitrary measurable POVMs are allowed within each block. The cost counts copies of the whole state. The strict constant-logarithmic criterion is \(g>1/(2^k+1)\); equality has exponent one, and at or below the threshold both budgets diverge at fixed error on the same good family. The scalar `sufficientBlockSize` results supply the choice \(\max\{1,\lceil\log_2(1/g)\rceil\}\) and its \(O(1+\log(1/g))\) bound.

## Notation and protocol conventions

| Manuscript | Lean representation and interpretation |
| --- | --- |
| \(d,n,D=d^n\) | `QuditIndex d n = Fin n → Fin d` indexes the computational basis. There are \(n\) sites in one copy, each of integer dimension \(d\ge2\). The asymptotic cutoff can be enlarged to \(n\ge1\). The tensor algebra also makes sense at \(n=0\). |
| \(a,b,g\) | \(a\) is the acceptance fidelity and \(b\) the rejection fidelity, with \(0<b<a\le1\). The normalized gap is \((a-b)/(1-b)\). Row `PROMISE` gives the two closed promise classes. |
| \(j,r,\gamma_j(d),r_d(g)\) | `Manuscript.gamma d j` and `Manuscript.criticalDegree d g` apply the generic geometric-base functions at \(d+1\). `criticalDegree_eq_min` realizes the least strict crossing. Zero degree, unit fidelity and equality at a step point are included. Rows `STRICT`, `II.samples` and `S6` give the extremum and parity statements. |
| \(\varepsilon,\varepsilon_+\) | `criticalExcess d j (a,b)` is the signed offset (7). The closed scale uses \(\max(\varepsilon,0)\). `nearCriticalCostOrder` distinguishes the sign branches of (8); `nearCriticalScale_compare_costOrder` supplies the two comparisons. |
| \(\delta,\delta_\star,L_\delta\) | `BornProtocol.Valid` uses error probability at most \(\delta\) on each promise class. `Information.testingThreshold` is the exact ordered binary loss on \(0<\delta<1/2\). Cutoff-uniform estimates use \(0<\delta\le\delta_\star<1/2\). Rows `I.errors`, `V.threshold`, `V.conf`. |
| \(\psi,P_\psi,\mathcal G_n\) | `spherePureVector` converts a unit sphere vector into the pure target. Its rank-one projector enters `pureTargetFidelity`. `CompactHaarTypical` includes convergence of the canonical sphere probabilities to one and a unitary-orbit probability identity. The fixed-threshold result also gives an exponential failure estimate. |
| \(N_{\rm exp},N_{\max}\) | `ProductBudget.expectedBudget` takes the infimum over valid protocols of their worst promised-input extended expectation. `ProductBudget.maximumBudget` takes the least feasible natural cap or infinity if none exists. `NearCriticalBudgetBounds` contains both inequalities and an actual feasible integer cap. Rows `I.exp` and `I.max`. |
| Score mean and second moment | Rows `III.samples`, `Eq.S33` and `Eq.S34` connect the operator moments to the actual Born record law of the full input state. S8 controls the mean and full second moment on the same event. |
| Finite dual and infinity atom | Sections II–VII use a finite signed comparison measure with an infinity atom. Row `S6` gives the extremal envelope and alternation results. Rows `WIENER`, `S30` and `TABLE-S1` identify boundary mass \(F(1)\), exact signed moments, normalized primal polynomials and full infinite-tail checks. |

In `PaperHistoryProduct`, the allowed action at a continuing history is a whole product POVM. All local factors are fixed before that copy is read. Earlier records and the seed determine subsequent actions and the stopping rule. Conditioning at each new copy uses the same arbitrary global density matrix \(\rho\) on the whole tensor product. For a measurable rectangle the probability is the trace of \(\rho\) against a tensor-product effect, which retains entanglement in \(\rho\). The mathematical input type `QIT.State` includes positivity and unit trace. The shell and mixture witnesses in `IV.states`, `IV.calib` and `S19` inhabit this physical type; the signed Hermitian kernels serve to estimate their difference.

For the extended expected cost, `BornProtocol.expectedCopies` integrates over the seed and Born records. `expected_truncations` identifies it with the supremum of finite truncations even when the expectation is infinite. Validity requires almost-sure termination in each promised world, and the deterministic cap constrains every legal path, including probability-zero paths. The infimum over an empty family of valid protocols in the extended nonnegative reals is infinity. The matching upper theorem explicitly supplies a finite-cap witness. The lower proof first constructs a common Haar-typical event controlling the entire frame family and a target-dependent hard pair, then quantifies over the measurement and the protocol. Complete MUBs enter only the optional finite-ensemble realization. The unconditional upper construction uses Pauli readout for \(d=2\) and Haar bases for \(d\ge3\).

## Supplemental statements

The detailed table has one canonical row for each numbered statement S1–S33. Additional rows identify component formulas, proof steps, specializations and public aliases. The coverage column distinguishes theorem statements, definitions and conventions, conditional claims, proved representations, independent exact checks, proof components, illustrations and material outside the formal scope. An `API.*` row points to a Lean declaration and adds no separate paper theorem.

| Supplementary-material range | Content and exports |
| --- | --- |
| S1–S7 | Interpolation, envelope duality, alternating finite optimal dual, uniqueness/rationality and elementary decay. `S7_decay` has \(q>2\); the later sharp theorem covers every \(q>1\). |
| S8–S15 | `S8_Haar_quantitative` and `S8_Pauli_quantitative` give the mean and full second moment on one measurable family with inverse-cube tolerance. The qualitative `S8_Haar` and `S8_Pauli` express convergence. Gaussian chaos, orbit Gram control, graph contraction and the normal-order remainder support the score proofs. With a supplied complete MUB, `S15_quantitative` is the quantitative score result, `S15_protocol_quantitative` supplies the executable protocol, and `S15_basis_upper` is the basis-budget result. |
| S16 | `S16_kernel_moments`: signed rank-one/complement kernel moments and frame bounds for arbitrary probability ensembles. |
| S17 | `S17`: arbitrary trace-one local matrix Weyl-shell identity and the original dual-state residual. |
| S18 | `S18_sphere`, `S18_Haar`, `S18_zero_radius`: one all-frame event covers every allowed product POVM, including zero radius. |
| S19 | `S19`, `S19_background`: same-target calibrated hard states, promises, ordered denominator floor, reference L² and KL. |
| S20 | `S20_high_low`, `S20_low_high`: arbitrary-kernel stopped information in the parity-selected direction. |
| S21 | `S21` / `tolerance_testing_bounds`: exact testing-scale bounds for actual optimized product budgets, including exponential typicality. |
| S22 | `S22` / `tolerance_hierarchy`: the logarithmic fixed-cutoff form on exponentially typical compact targets. For the exact \(L_\delta\) form on \(0<\delta<1/2\), also follow `S21` / `tolerance_testing_bounds`. The confidence cutoff follows the target family and dimension cutoff. |
| S23 | Fixed physical partition hierarchy and strict threshold criterion. |
| S24–S29 | Blaschke exact moments and L¹ norm, sharp lower bound, rational tail, oscillatory integral, sharp upper bound and sharp rate/root limit. `S25` is the infinite comparison-dual lower bound. |
| S30 | A finite certificate proves the full infinite envelope optimum and unique normalized optimizer. |
| S31 | Existence of a canonical rational certificate at every degree. |
| S32 | Explicit finite-stage exact search terminates and returns the exact value and unique optimizer. |
| S33 | Real low-degree formulas in their stated ranges and the qubit quadratic specialization. |

For **S27**, `oscillatory_integral_bound` bounds the unnormalized integral by
\((4C+12S+V)/\sqrt m\), where \(V\) is the integral of the amplitude-derivative
norm. Dividing the integral and bound by \(2\pi\) gives the paper's normalized
form. `upperCandidate_oscillatory_integral` in
`LocalCertification/Asymptotic/OscillatoryCandidate.lean` proves this normalized
application, with `upperOscillationConstant` including \(1/(2\pi)\), and
`upperCoefficient_bound` connects it to the actual coefficients.

## Representation bridges

**Measurable POVMs and refinement.** `MeasurablePOVM` is a normalized positive matrix-valued measure on an arbitrary measurable outcome space, with its actual Born measure. The trace reference and matrix Radon–Nikodym density are proved. Product constructions preserve original outcome labels. The eigenvalues of the local trace density are measurable in decreasing order. Polynomial projectors isolate each distinct eigenvalue, including repeated eigenspaces. Projecting the coordinate vectors and discarding zero Gram–Schmidt residuals gives measurable orthonormal eigenvectors. The corresponding eigenvalue-weighted rank-one projectors reconstruct the density. Zero eigenvalues have zero refined weight. Forgetting the spectral indices recovers the original effects, reference measure and all-state Born laws. The independent square-root column identity remains available.

**Refined residual versus original-label L².** The same original finite-dual coefficients, target and state pair are retained. Let \(D=d^n\), let \(\nu_{\rm ref}\) denote `productRefinementReference`, and let \(B_s\) be the literal signed complement kernel. The definition `dualResidualQuadratic` is

\[
R_\psi=D^2\int\bigl(\operatorname{Re}\operatorname{Tr}[(P_\psi-I/D)B_s]\bigr)^2\,d\nu_{\rm ref}(s).
\]

For the original dual pair, with \(c=\texttt{infinityWeight}/\texttt{dualNormalization}\), the proved chain is

\[
\int(f_H-f_L)^2\,d\nu_{\rm original}
\;\le\;\int(f_H^{\rm ref}-f_L^{\rm ref})^2\,d\nu_{\rm ref}
\;=\;c^2R_\psi
\;=\;c^2H_T(\psi).
\]

Here \(\nu_{\rm original}\) is the trace reference of the original product POVM. The first step is `product_referenceL2_sq_le_localRefinement`, and the refined equality is `dualStates_refined_difference_sq_integral`; together they give `dualStates_product_referenceL2_sq_le`. In `MeasurablePOVMFrameScore.lean`, `dualResidualQuadratic_eq_productFrameSphereScore` proves the final equality with the actual refined frame. It does not assert equality between coarse original-label L² and the frame score. No hard pair is selected after the measurement.

**Complex frames and physical observables.** `integralComplexMatrixFrame_eq_real_on_hermitian` identifies complex and real frame actions on Hermitian Hilbert–Schmidt inputs. Both \(zz^\dagger-I\) and \(P_\psi-I/D\) are Hermitian. The identification is restricted to that subspace; it is not an identity on arbitrary complex matrices. Complex tensor frames provide the finite-dimensional net, and their real restrictions act on these physical observables.

**Uniformity over measurements.** Every actual local refined frame belongs to `canonicalRankOneFrames`. The compact closure supplies a closed parameter family, while finite net centers remain actual realizable frames. `CanonicalProductFrameWitness` chooses a genuine probability ensemble for each center. This needs no measurable selection in the frame parameter and makes no claim that every closure point has such a witness. The Gaussian tail cutoff precedes all centers. The common sublevel set is closed even for an uncountable frame family; the probability estimate uses a finite net.

**History-kernel representation.** `PaperHistoryProduct` independently specifies
measurable global product POVMs only at continuing full histories.
`POVMKernel.exists_product_factors` proves measurability of local factors from
global event effects. `Paper.history_model_compilation` constructs an actual
setting-family protocol preserving Born laws, stopping times, decisions and
legal paths; causal finite-prefix reconstruction retains the original labels.
The converse setting-to-history embedding is also proved.
`Paper.history_budget_equivalence` identifies the two independently defined
extended expected budgets, finite-cap feasibility predicates and maximum
budgets exactly, in each declared universe. No finiteness, standard-Borel,
finite-expectation or nonempty-outcome premise is added. A protocol with no
continuing context is compiled using an empty setting space.

**Original execution and physical blocks.** `OriginalProductProtocol.{u,v,w}` preserves literal seeds, selected settings, outcomes, full records, Born laws, expected costs, validity and caps on every legal path after universe alignment to `max u v w`. No finite-tree or standard-Borel hypothesis is imposed. Null seeds and zero-probability Born outcomes remain part of the deterministic cap condition; almost-sure termination does not imply finite expectation. The fixed-block representation additionally proves protocol and optimized-budget equalities and the physical target pullback, with the partition fixed outside the action space.

## Gaussian normalization and the variance bound

`pairedGaussian` supplies independent standard real coordinates. `complexCoordinate` uses \(z_i=(X_i+iY_i)/\sqrt2\), so the complex covariance is \(I\). For a probability reference \(\nu\) and an almost-everywhere Hermitian, a.e. strongly measurable, Hilbert–Schmidt-bounded matrix ensemble \(B_s\), `measurableQuadraticEnsemble` is

\[
Q_G(z)=\int\bigl(\operatorname{Re}(z^\dagger B_s z-\operatorname{Tr}B_s)\bigr)^2\,d\nu(s),
\qquad
\mathbb E Q_G=v=\int\operatorname{Re}\operatorname{Tr}(B_s^2)\,d\nu(s).
\]

There is no extra dimension factor in this Gaussian definition. `MeasurableGaussianQuadraticVariance.lean` proves the actual variance identity by integrating the noncommuting covariance

\[
2(\operatorname{Re}\operatorname{Tr}(AB))^2
+2\operatorname{Re}\operatorname{Tr}(ABAB)
+4\operatorname{Re}\operatorname{Tr}(A^2B^2).
\]

Let \(D\) be the matrix dimension, \(T=\texttt{integralMatrixFrame}\ \nu\ B\) the real Hilbert–Schmidt frame and \(S=\int B_s^2\,d\nu(s)\). `measurableQuadraticEnsemble_variance_le_scalar` in `MeasurableGaussianFrameBound.lean` proves

\[
S=\frac vD I,\quad \|T\|\le\frac{L^2}{D},\quad v\ge0
\quad\Longrightarrow\quad
\operatorname{Var}Q_G\le\frac{2L^2v+6v^2}{D}.
\]

The companion `measurableQuadraticEnsemble_variance_le_eight` uses the additional proved bound \(v\le L^2\) to obtain \(\operatorname{Var}Q_G\le8L^2v/D\). For the actual product kernels,

\[
D=d^n,\qquad L=\sum_{k\in J}|\theta_k|,\qquad
v=\sum_{k\in J}\frac{\theta_k^2}{\binom nk(d-1)^k}.
\]

Their moment and frame bounds, including \(0\le v\le L^2\), are proved for isotropic unit-vector product ensembles, \(d\ge2\) and supported radii \(k\le n\). Signed weights are allowed. The unit-mass condition is needed for the trace-one/radial sphere bridge, rather than as a further Gaussian scaling convention. No commutativity or simultaneous diagonalization is assumed.

## Proof routes

The **S18 analytic route** combines literal signed kernel moments, noncommuting Wick covariance, arbitrary-measure integration, the variance estimate above, and a genuine quartic polynomial with its hypercontractive tail. With the same Gaussian sample, \(t=\|z\|^2/D\) and the sphere direction \(\psi\), the proved radial identity is

\[
Q_G=t^2H_T(\psi)+(t-1)^2,\qquad
H_T(\psi)=D^2\langle\operatorname{HS}(P_\psi-I/D),T\operatorname{HS}(P_\psi-I/D)\rangle.
\]

The paper takes a radial error of n⁻⁴. `Quantum.frame_family_score_of_quartic_radius` gives its explicit uniform bound `((1+1/n)/(1−n⁻⁴)² + 1/n) v`. The main uniform-event proof allows n⁻², giving the factor 1+6/n. The local covering dimension bound 2d⁴ includes real and imaginary coordinates; the paper uses d⁴ for Hermitian coordinates. Both give log-cardinality O(n²).

The net uses the scaled error \(D^2\|T-W\|\le v/n\), cardinality at most \((1+2DL^2n^2/v)^{2d^4n}\), and the eventual entropy bound \(\exp(A n^2)\). Common-radius and off-net estimates produce the closed all-frame sphere event with factor \(1+6/n\) and failure at most \(\exp(-(\log d)n^3/16)\), followed by the actual Haar orbit statement.

The **general lower bound** uses the spectral refinement of each local POVM. On the common shell event, the reference norm of the calibrated difference on the refined records is at most \(\beta\sqrt{(1+6/n)v_n}+e\sqrt{2D}\). The second state's positive density floor gives \(\sqrt{\chi^2}\le \|\Delta\|_{\nu^{-1}}/\sqrt\beta\) in the parity-dependent order of S19. Ordered KL is bounded on the refined laws and contracts under the map that forgets the refinement indices. Stopped testing information then bounds both optimized costs. The degree-zero hard pair in the fixed-threshold hierarchy and the radius-zero mixture in the crossover proof have separate constructions.

For **S110**, `S22_weight_estimates` covers both radial coefficient sequences with a common constant. It controls all weights \(L<w\le n\), the normalized absolute mass over all Weyl strings, and the square root of the normalized squared mass over high-weight strings. The high-weight statements also cover an empty range.

The **stopped-information proof** uses variational KL and Markov-kernel composition, full finite histories, active-count prefix bounds and actual expected \(\min(T,m)\). Separate source and target termination yield the terminal decision limits; extended monotone convergence retains infinite expectations.

The **upper bound** embeds the actual Haar/Pauli basis protocol through `maximumBudget_le_basisBudget_universe`, then uses the enlarged class's own expected-budget/maximum-budget inequality. This inclusion transfers an upper bound only. Conditional MUB constructions keep their supplied `CompleteMUB d` hypothesis.

The **self-contained sharp asymptotic proof** uses Blaschke coefficients, Parseval, weighted Cauchy–Schwarz, oscillatory polynomial bounds, the infinite comparison dual and strict inversion. The Wiener construction expresses the finite dual extremum using an absolutely summable series with a repeated node and the boundary mass at one. Its real and complex formulations are related by coefficient projection and lifting. The two-sided interpolation estimates concern the repeated positive real node used here.

The **certificate search** uses explicit finite staged arrays, a Boolean rational checker, exhaustive coverage of records and canonical certificate existence. It returns the first passing record at the first successful stage and proves termination. Runtime checks include the small \(q=3/2,r=0\) search and the supplied degree-0-through-10 certificates; they do not enumerate the enormous degree-10 coverage stage.

## Verification and scope

The formal check entries inspect elaborated types, transitive axioms and positive and negative proof dependencies. The [Gaussian bridge](docs/gaussian-bridge.md) provides the analytic log-Sobolev and hypercontractivity results.

**Equation (S22).** `Extremal.decayPolynomial_eq_alternating_sum` and `Extremal.decayPolynomial_eq_shifted_binomial` identify the trial polynomial with both printed polynomials. The signed shifted binomial uses composition with X−1, which also gives the correct value at zero. Proposition S22 is a distinct confidence statement.

**Dimension parameters.** `Paper.S25` and `Paper.S25_coefficient` take real d > 0. `Paper.S30`, `Paper.S31`, `Paper.S32_termination` and `Paper.S32_correct` take rational d > 0 and the checker uses base d+1. `Paper.S33` and `Paper.low_degree_values` state each formula in its own range, including the separate qubit value.
