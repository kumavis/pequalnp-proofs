# Projective-plane incidence circuits through order 365

L-meta-2008 asks for `Nq ≤ 100s`, where a plane of order `q` has `N = q² + q + 1` points and as many lines, and `s` is the size of a normalized binary monotone circuit. The circuit accepts every incident point–line singleton pair. It rejects every incidence-free input with at most `q` selected lines.

For every such plane of order `q ≥ 2`, gate elimination gives `11N ≤ 3s + 18q + 7`. This implies the requested bound throughout `101 ≤ q ≤ 365`, for every circuit satisfying the hypotheses. At the prime order 359 it gives at least 471,728 gates against a target of 463,976. At the prime order 367 it gives 493,005 against 495,660. The proof leaves the unrestricted case `q > 365` open.

## Reading the proof

- [`clean_bound`](TriangularBound.lean) counts gates saved by restricting the plane to a grid formed by two pencils of lines and eliminating a triangle of point inputs. [`through_365` and `residual_iff_365`](Through365.lean) derive the finite range and relate the remaining statement to the original desk problem.
- [`exact_separate_outputs`](ExactRows.lean) proves the exact `Nq` cost when all point rows must be reported separately. The desk circuit has one output. [`DeskExtraction.lean`](DeskExtraction.lean) gives a sufficient condition on its AND gates for extracting the rows at bounded cost.
- [`desk_ninety_three`](SourceFraction.lean) shows that in any circuit below the target at `q ≥ 200`, more than 93% of incidences admit a change of input background that forces a different source gate for that same incidence. The change may depend on the incidence and the gate. Counting distinct gates across these changes remains open.

The [research note](research-note.txt) explains the proofs, the other structural bounds, and two finite experiments. Earlier project reductions cover [exact operand tags](https://github.com/open-goat/pequalnp-proofs/pull/4405) and a [finite-grid formulation](https://github.com/open-goat/pequalnp-proofs/pull/4734).

## Reproducing the checks

From the repository root, use the pinned Lean 4.36.0 toolchain and mathlib recorded in `lean/lake-manifest.json`.

```sh
(cd lean && lake exe cache get && lake build PEqualNP.Defs)
cd notes/l-meta-2008
./check.sh ../../lean
python3 template_circuit.py | diff - template-check.txt
python3 source_check.py | diff - source-check.txt
```

The checker compiles all 73 Lean modules from source in a temporary directory and runs `leanchecker` on each module. The terminal theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The Python scripts use the standard library. The large-order template estimate is a symbolic calculation.
