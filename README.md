# Local State Certification in Lean

This library formalizes results from *Sharp Transitions of Copy Complexity in Local Certification of Typical Pure States* by Yimeng Cao and Ge Bai. It studies the number of fresh copies needed to test a fidelity promise using local measurements on a Haar-typical pure target state.

## Main results

Import `LocalCertification.Paper` to use these declarations in the `LocalCertification.Paper` namespace.

| Declaration | Result |
| --- | --- |
| `theorem_1` | For fixed integer local dimension d ≥ 2 and thresholds 0 < b < a ≤ 1, the two optimal copy budgets scale as nʳ log(1/δ). One Haar-typical target family works uniformly over 0 < δ ≤ δ★ for each fixed δ★ < 1/2. The exponent is the first strict crossing of the critical sequence. |
| `corollary_2` | One open neighborhood of a critical threshold pair, one typical target family and one size threshold work as both thresholds and δ vary. For positive excess ε the scale is min(nʲ/ε², nʲ⁺¹), and for ε ≤ 0 it is nʲ⁺¹. Both budgets carry the factor log(1/δ). |
| `theorem_3`, `theorem_3_wiener` | For integer d ≥ 2 the critical values have order (d+1)⁻ʲ/√j. Writing L = log base (d+1) of 1/g, the strict crossing index is L − ½ log base (d+1) of L + O(1) as g tends to zero. The two proofs use Euler moments and Wiener interpolation. |

The general lower bound allows arbitrary measurable local product POVMs, classical randomization, adaptation between copies, and random stopping. The expected cost is the worst expected number of copies over promised inputs. The maximum cost caps every legal path, including paths of probability zero. The upper bound constructs a nonadaptive protocol with a deterministic cap. The optional finite-ensemble construction assumes a complete family of mutually unbiased bases.

The [proof guide](PAPER_MAP.md) explains the model, quantifiers, and proof constructions. The [correspondence table](docs/paper-map.tsv) pairs numbered results and equations with Lean declarations and source files.

## Build and check

The supported verification environment is x86-64 Linux, including Ubuntu under WSL. Install Python 3.10 or later, Git, curl, bubblewrap and the Elan toolchain in `lean-toolchain`. In a Git checkout or extracted source directory, run:

```sh
python3 -B scripts/acquire.py --output ../certification-dependencies
python3 -B scripts/verify.py --mode full --dependencies ../certification-dependencies/state.json --output ../certification-full
```

Use new output directories outside the source tree. The acquisition command fetches pinned dependencies, uses the matching Mathlib cache and compiles the required Lean-QIT imports. An intact dependency directory from the same lock files can be reused by passing its `state.json` to the full command. The full verifier checks dependency integrity, compiles every production and support module, then runs statement, proof-route, certificate and transitive-axiom checks in a read-only source sandbox without network access. It records commands, logs and a receipt in the output directory.

To examine the complete types and direct dependencies for selected paper results after a full build, run:

```sh
python3 -B scripts/inspect_paper_row.py --build ../certification-full --dependencies ../certification-dependencies/state.json T1 C2 T3 Eq.S22
```

On Windows, the PowerShell launcher runs the same verification in WSL. Install the Linux prerequisites in the selected distribution:

```powershell
.\scripts\verify.ps1 -Acquire -Output '..\certification-dependencies'
.\scripts\verify.ps1 -Mode full -Dependencies '..\certification-dependencies\state.json' -Output '..\certification-full'
```

Use `-Distribution` to select an installed WSL distribution explicitly. Run the verifier's own regression tests with `python3 -B -m unittest discover -s scripts/tests -v`. The four native PowerShell launcher tests can also be run on Windows using `python -B -m unittest discover -s scripts/tests -p test_launcher_windows.py -v`.

## Sources and license

The project uses Lean 4, Mathlib and Lean-QIT. Exact revisions are in the [dependency lock](lake-manifest.json) and [dependency list](docs/dependencies.json). The [source ledger](docs/upstream-sources.tsv) identifies adapted or extracted third-party files. See the [Gaussian bridge](docs/gaussian-bridge.md) for the spectral Gaussian semigroup construction.

Original software, documentation and local contributions use the [Apache License, Version 2.0](LICENSE). Upstream copyright, license texts and notices are listed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

**Paper** · Yimeng Cao and Ge Bai, *Sharp Transitions of Copy Complexity in Local Certification of Typical Pure States*. [Source repository](https://github.com/cymhit/local-state-certification-lean).
