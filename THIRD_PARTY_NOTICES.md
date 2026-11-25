# Third-party notices and license scope

Original project code, documentation and local contributions, including changes to
upstream software, are licensed under the [Apache License, Version 2.0](LICENSE).
The following notices identify the upstream material, its authors and the license
terms that accompany it.

## Bundled third-party source

| Source | Exact revision | Repository |
| --- | --- | --- |
| gaussian-hilbert | `4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e` | https://github.com/mrdouglasny/gaussian-hilbert |
| markov-semigroups | `acf649108ea2222f4a8544a2782f448cb502492a` | https://github.com/mrdouglasny/markov-semigroups |
| gaussian-field | `dc2b3b8378b2b7e33eaa8b61d6e943de11ff3f33` | https://github.com/mrdouglasny/gaussian-field |
| Lean-QIT | `a081b343123a6262b0fa4371d3fec7386757ff88` | https://github.com/QuAIR/Lean-QIT |

The package includes 27 attributed source selections, each adapted or extracted.
Their original copyright and author notices, including those of Michael R. Douglas
and the QuAIR Team, appear in the source headers alongside the modification
or extraction notices. The [file-level source ledger](docs/upstream-sources.tsv)
records the source paths, commits, classifications and applicable licenses.

The five retained gaussian-hilbert whole-file selections explicitly state
Apache-2.0. The pinned markov-semigroups repository supplies Apache-2.0 terms,
preserved at `support/gaussian/licenses/MarkovSemigroups-LICENSE`; those terms also
cover its headerless `EuclideanFinBE.lean` file. The gaussian-field selections
carry Apache notices; its short original license is preserved at
`support/gaussian/licenses/GaussianField-LICENSE`. The QIT adaptation
`CertificationGaussian/MatrixKroneckerNorm.lean` preserves QuAIR copyright and
author attribution and the pinned Apache license at
`support/gaussian/licenses/QIT-LICENSE`. The copy at `licenses/Apache-2.0.txt`
preserves the MarkovSemigroups license and its original copyright notice.
The HermiteIntegral extraction preserves the original source's 2025 copyright year.

The earlier copyright-only `GaussianHilbert/HypercontractivityFromBE.lean`
implementation has been replaced by a new implementation over explicitly licensed
foundations. It is neither included nor fetched. The source ledger identifies the excluded implementation. [docs/gaussian-bridge.md](docs/gaussian-bridge.md) records the
licensed foundations and mathematical construction.
The replacement is a local contribution licensed under Apache-2.0.

## External build dependencies

The exact public revisions in `lake-manifest.json` and `docs/dependencies.json`
are acquired at build time; their complete source trees and compiled caches are
not bundled. Retained license copies are in `licenses/lean`, `licenses/mathlib`,
`licenses/QIT`, `licenses/aesop`, `licenses/batteries`, `licenses/Cli`,
`licenses/importGraph`, `licenses/LeanSearchClient`, `licenses/plausible`,
`licenses/proofwidgets`, and `licenses/Qq`. Lean's additional notices are in
`licenses/lean/LICENSES`. QIT is both an external dependency and a bundled
adaptation source. The trees at the four bundled-source revisions listed above
contain no separate upstream NOTICE file.

## Project materials

The root license covers original software, tests, build scripts, configuration,
documentation and local contributions. Existing upstream notices remain attached
to their respective materials. The separately distributed manuscript and its
figures have their own rights.
