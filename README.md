# Erdős formal proofs

Lean 4 proofs of three declarations from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
linked from that repository via `@[formal_proof using lean4 at ...]`.

| formal-conjectures declaration | category | proof here |
|---|---|---|
| `Erdos23.erdos_23.variants.n1` (`ErdosProblems/23.lean`) | test | `Erdos23.erdos_23_n1` in `ErdosFormalProofs/Erdos23N1.lean` |
| `Erdos23.blowupC5_tight` (`ErdosProblems/23.lean`) | test | `Erdos23.blowupC5_tight` in `ErdosFormalProofs/Erdos23BlowupC5.lean` |
| `Erdos1171.erdos_1171.variants.mono_k` (`ErdosProblems/1171.lean`) | API | `Erdos1171.mono_k` in `ErdosFormalProofs/Erdos1171MonoK.lean` |

Each file copies the needed definition (`blowupC5`, `OrdinalMultiColorRamsey`) verbatim from
formal-conjectures (commit `ea8e3e1`), and each theorem statement is identical to the
repository statement. Toolchain and Mathlib revision match formal-conjectures
(Lean v4.33.1, Mathlib `0df444a`).

**These are not resolutions of the open problems.** Erdős 23 and Erdős 1171 remain open; these
are the n = 1 case and tightness example of Erdős 23, and a monotonicity lemma for 1171.

## Verify

```
lake exe cache get
lake build
lake env lean Axioms.lean   # expect only [propext, Classical.choice, Quot.sound]
```

`VERIFICATION.md` records the checks: the axiom output, the comparison with the
formal-conjectures statements, and the computations in `checks/`.

## Proof sketches

**`blowupC5_tight`.** A 2-colouring of a bipartite H ≤ blowup(C₅) forces deletion of every
monochromatic edge. With aᵢ, bᵢ the colour counts in part i (aᵢ + bᵢ = n), there are
S = Σ (aᵢaᵢ₊₁ + bᵢbᵢ₊₁) of them, and

  n·(S − n²) = 2·(a₀a₁a₄ + a₁a₂a₃ + a₁b₃b₄ + a₃a₄b₁ + b₀b₁b₄ + b₁b₂b₃) ≥ 0.

**`n1`.** If a vertex v has two neighbours p, q, colour N(v) against the rest: monochromatic
edges lie in the 2-element set V ∖ {v, p, q}. Otherwise G is a matching and colouring by
"has a smaller neighbour" leaves no monochromatic edge.

**`mono_k`.** Push a (j+1)-colouring into k+1 colours with `Fin.castLE`; a colour-(i+1)
witness has #A = 3 > 1, so i < j. Note: as stated in formal-conjectures, the hypothesis and
conclusion of `mono_k` elaborate at independent universe levels (`mono_k.{u_1,u_2}`), so the
proof includes a universe-transfer lemma (`Erdos1171.transfer`).

## License
Apache 2.0 (same as formal-conjectures).

## How to cite

DOI: [10.5281/zenodo.24572643](https://doi.org/10.5281/zenodo.24572643) (all versions; v1.0 is
[10.5281/zenodo.24572644](https://doi.org/10.5281/zenodo.24572644)). See `CITATION.cff`.
