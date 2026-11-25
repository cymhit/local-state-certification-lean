# Gaussian hypercontractivity

`GaussianHilbert/HypercontractivityFromBE.lean` is a local Apache-2.0 implementation. It obtains the Gaussian log-Sobolev inequalities from the Bakry–Émery structures. Equality of the spectral and concrete Mehler operators transports the concrete Gaussian hypercontractive estimate to the spectral OU action. At time zero the Nelson constraint forces p = 2 and the operator is the identity.

| Foundation | Fixed upstream source | Facts used |
| --- | --- | --- |
| Gaussian spectral/Mehler action | gaussian-hilbert `4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e`, `GaussianHilbert/OUEigenfunctions.lean` | `mehlerOp_apply`, `mehlerOp_eq_ouSemigroupAct` |
| Gaussian Dirichlet-Markov semigroup | markov-semigroups `acf649108ea2222f4a8544a2782f448cb502492a`, `MarkovSemigroups/Instances/WorkInProgress/EuclideanHypercontractive.lean` and its imports | `stdGaussianFin_satisfiesLogSobolev`, `stdGaussianFin_isHypercontractive`, `ouSemigroupFinLp_coeFn_ae`, `ouSemigroupFinLp_zero` |
| Log-Sobolev implication and operator equality | The same Apache-covered MarkovSemigroups foundation and pinned Mathlib | `BakryEmerySpace.satisfiesLogSobolev`, `ContinuousLinearMap.ext`, `Lp.ext_iff` |


The [source ledger](upstream-sources.tsv) identifies the earlier gaussian-hilbert source at this path as excluded. That copyright-only implementation is neither distributed nor fetched. The local construction uses the public interface and the licensed foundations above. Original attribution accompanies the adapted foundation files.

The [bridge check](../checks/GaussianBridgeReplacement.lean) states the log-Sobolev and hypercontractivity types independently, checks the zero-time consequence and audits the declarations in the bridge module.
