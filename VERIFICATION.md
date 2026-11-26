# Verification record

Checked on 2026-11-26. None of this resolves Erdős Problem 23 or Erdős Problem 1171; both
remain open. The results are the n = 1 case and the tightness example of Erdős 23, and a
monotonicity lemma for Erdős 1171.

## Theorems (checked by Lean)

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (commit
`0df444a360eaa60ab8c11dca51a86af692955474`), the same as google-deepmind/formal-conjectures at
commit `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`.

`lake env lean Axioms.lean`, GitHub Actions run
https://github.com/tommac/erdos-formal-proofs/actions/runs/45903233267 (Lean 4.33.1,
x86_64-unknown-linux-gnu), verbatim. That run built an earlier commit, `e30cca2`, whose Lean
files are byte-identical to this one; this commit only adds documentation, metadata and
`checks/`, and its own CI run repeats the build:

```
'Erdos1171.mono_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos23.erdos_23_n1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos23.blowupC5_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The source files contain no `sorry`, `native_decide`, `axiom` or
`set_option debug.skipKernelTC`.

| Theorem here | formal-conjectures declaration |
|---|---|
| `Erdos23.erdos_23_n1` | `Erdos23.erdos_23.variants.n1` |
| `Erdos23.blowupC5_tight` | `Erdos23.blowupC5_tight` |
| `Erdos1171.mono_k` | `Erdos1171.erdos_1171.variants.mono_k` |

**Statements.** `checks/statements.py` compares each statement and the two copied definitions
with formal-conjectures at `ea8e3e1`, whitespace-normalised. Output:

```
erdos_23.variants.n1: identical
blowupC5_tight: identical
mono_k: identical
def blowupC5: identical
def OrdinalMultiColorRamsey: identical
ALL IDENTICAL
```

**Universes of `mono_k`.** With `set_option pp.universes true`, `#check @Erdos1171.mono_k`
shows `Erdos1171.mono_k.{u_1, u_2}`: the hypothesis is about `OrdinalMultiColorRamsey.{u_1}`
and the conclusion about `OrdinalMultiColorRamsey.{u_2}`. The statement is the
formal-conjectures text, so the upstream declaration has the same independent levels. The
proof covers this with `Erdos1171.transfer`.

## Certified computations (scripts and output on record; not proofs)

`checks/checks.py` (Python 3, sympy 1.14). Output:

```
identity n(S - n^2) - RHS expands to: 0
blowupC5 n=1: 5 edges, minimum deletions over all 2-colourings = 1, n^2 = 1, ok = True
blowupC5 n=2: 20 edges, minimum deletions over all 2-colourings = 4, n^2 = 4, ok = True
blowupC5 n=3: 45 edges, minimum deletions over all 2-colourings = 9, n^2 = 9, ok = True
n1: 1024 graphs on 5 vertices, 388 triangle-free, max over them of min deletions = 1, ok = True
```

- The identity is n(S − n²) = 2(a₀a₁a₄ + a₁a₂a₃ + a₁b₃b₄ + a₃a₄b₁ + b₀b₁b₄ + b₁b₂b₃), with
  bᵢ = n − aᵢ and S = Σᵢ (aᵢaᵢ₊₁ + bᵢbᵢ₊₁), indices mod 5.
- For a 2-colouring, the edges that must be deleted are the monochromatic ones, so the
  minimum over all colourings is the least number of deletions that leaves a bipartite
  graph.

## Claims (not checked by either of the above)

- The proof sketches in `README.md` describe the Lean proofs informally.
- Erdős 23 asks whether every triangle-free graph on 5n vertices becomes bipartite after
  deleting at most n² edges; it is open. Erdős 1171 is open for general k.
