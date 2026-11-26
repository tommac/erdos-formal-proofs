import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Erdős 23 — `erdos_23.variants.n1`: every triangle-free graph on 5 vertices becomes
bipartite after deleting at most one edge. -/

open SimpleGraph

namespace Erdos23

open scoped Classical in
/-- If a 2-colouring `c` has at most one monochromatic `G`-edge, we are done. -/
lemma of_coloring (G : SimpleGraph (Fin 5)) (c : Fin 5 → Fin 2)
    (hc : ∀ x y x' y', G.Adj x y → c x = c y → G.Adj x' y' → c x' = c y' →
      s(x, y) = s(x', y')) :
    ∃ (H : SimpleGraph (Fin 5)), H ≤ G ∧ H.IsBipartite ∧
      (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  classical
  let H : SimpleGraph (Fin 5) :=
    { Adj := fun u v => G.Adj u v ∧ c u ≠ c v
      symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
  refine ⟨H, fun u v h => h.1, ⟨Coloring.mk c fun h => h.2⟩, ?_⟩
  rw [Finset.card_le_one]
  intro e he e' he'
  simp only [Finset.mem_sdiff, mem_edgeFinset] at he he'
  revert he he'
  refine Sym2.ind (fun x y => ?_) e
  refine Sym2.ind (fun x' y' => ?_) e'
  intro he he'
  simp only [mem_edgeSet] at he he'
  have h1 : c x = c y := by by_contra h; exact he.2 ⟨he.1, h⟩
  have h2 : c x' = c y' := by by_contra h; exact he'.2 ⟨he'.1, h⟩
  exact hc x y x' y' he.1 h1 he'.1 h2

/-- The complement of three distinct points of `Fin 5` has only two points. -/
lemma third (v p q x y z : Fin 5) (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hx : x ≠ v ∧ x ≠ p ∧ x ≠ q) (hy : y ≠ v ∧ y ≠ p ∧ y ≠ q)
    (hz : z ≠ v ∧ z ≠ p ∧ z ≠ q) (hxy : x ≠ y) : z = x ∨ z = y := by
  revert v p q x y z; decide

/-- Two edges living in the 2-element complement of `{v, p, q}` coincide. -/
lemma pair_unique (v p q x y x' y' : Fin 5) (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hx : x ≠ v ∧ x ≠ p ∧ x ≠ q) (hy : y ≠ v ∧ y ≠ p ∧ y ≠ q)
    (hx' : x' ≠ v ∧ x' ≠ p ∧ x' ≠ q) (hy' : y' ≠ v ∧ y' ≠ p ∧ y' ≠ q)
    (hxy : x ≠ y) (hxy' : x' ≠ y') : s(x, y) = s(x', y') := by
  rcases third v p q x y x' hvp hvq hpq hx hy hx' hxy with h1 | h1 <;>
  rcases third v p q x y y' hvp hvq hpq hx hy hy' hxy with h2 | h2 <;> rw [h1, h2]
  · exact absurd (h1.trans h2.symm) hxy'
  · exact Sym2.eq_swap
  · exact absurd (h1.trans h2.symm) hxy'

open scoped Classical in
theorem erdos_23_n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  classical
  intro G hG
  have tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False := fun a b c hab hac hbc =>
    hG {a, b, c} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
  by_cases hdeg : ∃ v p q, p ≠ q ∧ G.Adj v p ∧ G.Adj v q
  · -- colour the neighbourhood of `v` with `1`, everything else with `0`
    obtain ⟨v, p, q, hpq, hvp, hvq⟩ := hdeg
    refine of_coloring G (fun x => if G.Adj v x then 1 else 0) ?_
    -- a monochromatic edge avoids `v`, `p`, `q`
    have avoid : ∀ x y, G.Adj x y → ((if G.Adj v x then 1 else 0 : Fin 2) =
        if G.Adj v y then 1 else 0) →
        (x ≠ v ∧ x ≠ p ∧ x ≠ q) ∧ (y ≠ v ∧ y ≠ p ∧ y ≠ q) := by
      intro x y hxy hc
      by_cases hx : G.Adj v x <;> by_cases hy : G.Adj v y <;> simp [hx, hy] at hc
      · exact (tri v x y hx hy hxy).elim
      · refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> rintro rfl
        · exact hy hxy
        · exact hx hvp
        · exact hx hvq
        · exact hx hxy.symm
        · exact hy hvp
        · exact hy hvq
    intro x y x' y' hxy hc hxy' hc'
    obtain ⟨hx, hy⟩ := avoid x y hxy hc
    obtain ⟨hx', hy'⟩ := avoid x' y' hxy' hc'
    exact pair_unique v p q x y x' y' hvp.ne hvq.ne hpq hx hy hx' hy' hxy.ne hxy'.ne
  · -- maximum degree ≤ 1: `G` is a matching, colour by "has a smaller neighbour"
    push Not at hdeg
    refine of_coloring G (fun x => if ∃ w, w < x ∧ G.Adj x w then 1 else 0) ?_
    have nomono : ∀ x y, G.Adj x y → ((if ∃ w, w < x ∧ G.Adj x w then 1 else 0 : Fin 2) =
        if ∃ w, w < y ∧ G.Adj y w then 1 else 0) → False := by
      -- WLOG `y < x`
      have key : ∀ x y, y < x → G.Adj x y →
          ((if ∃ w, w < x ∧ G.Adj x w then 1 else 0 : Fin 2) =
            if ∃ w, w < y ∧ G.Adj y w then 1 else 0) → False := by
        intro x y hyx hxy hc
        have hx : ∃ w, w < x ∧ G.Adj x w := ⟨y, hyx, hxy⟩
        rw [if_pos hx] at hc
        by_cases hy : ∃ w, w < y ∧ G.Adj y w
        · obtain ⟨w, hwy, hyw⟩ := hy
          exact (hdeg y x w (by rintro rfl; exact absurd (hwy.trans hyx) (lt_irrefl _))
            hxy.symm) hyw
        · rw [if_neg hy] at hc; exact absurd hc (by decide)
      intro x y hxy hc
      rcases lt_trichotomy x y with h | h | h
      · exact key y x h hxy.symm hc.symm
      · exact hxy.ne h
      · exact key x y h hxy hc
    intro x y x' y' hxy hc _ _
    exact (nomono x y hxy hc).elim

end Erdos23

