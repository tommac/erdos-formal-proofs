import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Erdős 23 — `blowupC5_tight`. Definition copied verbatim from
`FormalConjectures/ErdosProblems/23.lean`.

Proof: a bipartition `f` of `H` forces every `f`-monochromatic edge of the blow-up to be
deleted. With `a i` / `b i` the numbers of colour-0 / colour-1 vertices in part `i`,
the monochromatic edges number `∑ (a i * a (i+1) + b i * b (i+1))`, and the identity
`n * (∑ - n²) = 2 * (a0a1a4 + a1a2a3 + a1b3b4 + a3a4b1 + b0b1b4 + b1b2b3)` shows `∑ ≥ n²`. -/

open SimpleGraph

namespace Erdos23

def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

/-- The pure inequality behind the tightness. -/
lemma c5_ineq (n a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ) (hn : 0 < n)
    (h0 : a0 + b0 = n) (h1 : a1 + b1 = n) (h2 : a2 + b2 = n) (h3 : a3 + b3 = n)
    (h4 : a4 + b4 = n) :
    n ^ 2 ≤ (a0 * a1 + b0 * b1) + (a1 * a2 + b1 * b2) + (a2 * a3 + b2 * b3) +
      (a3 * a4 + b3 * b4) + (a4 * a0 + b4 * b0) := by
  have key : n * ((a0 * a1 + b0 * b1) + (a1 * a2 + b1 * b2) + (a2 * a3 + b2 * b3) +
      (a3 * a4 + b3 * b4) + (a4 * a0 + b4 * b0)) =
      n * n ^ 2 + 2 * (a0 * a1 * a4 + a1 * a2 * a3 + a1 * b3 * b4 + a3 * a4 * b1 +
        b0 * b1 * b4 + b1 * b2 * b3) := by
    zify at h0 h1 h2 h3 h4 ⊢
    have e0 : (b0 : ℤ) = n - a0 := by linarith
    have e1 : (b1 : ℤ) = n - a1 := by linarith
    have e2 : (b2 : ℤ) = n - a2 := by linarith
    have e3 : (b3 : ℤ) = n - a3 := by linarith
    have e4 : (b4 : ℤ) = n - a4 := by linarith
    rw [e0, e1, e2, e3, e4]; ring
  have : n * n ^ 2 ≤ n * ((a0 * a1 + b0 * b1) + (a1 * a2 + b1 * b2) + (a2 * a3 + b2 * b3) +
      (a3 * a4 + b3 * b4) + (a4 * a0 + b4 * b0)) := by rw [key]; omega
  exact Nat.le_of_mul_le_mul_left this hn

lemma ite_eq_fin2 (p q : Fin 2) :
    (if p = q then 1 else 0 : ℕ) =
      (if p = 0 then 1 else 0) * (if q = 0 then 1 else 0) +
      (if p = 1 then 1 else 0) * (if q = 1 then 1 else 0) := by
  fin_cases p <;> fin_cases q <;> rfl

lemma ite_add_fin2 (p : Fin 2) :
    (if p = 0 then 1 else 0 : ℕ) + (if p = 1 then 1 else 0) = 1 := by
  fin_cases p <;> rfl

lemma zmod5_add_one_add_one_ne (i : ZMod 5) : i + 1 + 1 ≠ i := by
  revert i; decide

lemma zmod5_add_one_ne (i : ZMod 5) : i + 1 ≠ i := by
  revert i; decide

open scoped Classical in
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  obtain ⟨c⟩ := hBip
  let f : ZMod 5 × Fin n → Fin 2 := c
  -- oriented monochromatic edges `(i, x) — (i+1, y)`
  let S : Finset (ZMod 5 × Fin n × Fin n) :=
    Finset.univ.filter fun t => f (t.1, t.2.1) = f (t.1 + 1, t.2.2)
  have hS : S.card ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => s((t.1, t.2.1), (t.1 + 1, t.2.2))) ?_ ?_
    · intro t ht
      have ht' : f (t.1, t.2.1) = f (t.1 + 1, t.2.2) := (Finset.mem_filter.1 ht).2
      simp only [Finset.mem_coe, Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet]
      refine ⟨?_, fun hadj => c.valid hadj ht'⟩
      rw [blowupC5, fromRel_adj]
      exact ⟨fun h => zmod5_add_one_ne t.1 (congrArg Prod.fst h).symm, by simp⟩
    · rintro ⟨i, x, y⟩ _ ⟨i', x', y'⟩ _ heq
      simp only [Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with ⟨⟨hi, hx⟩, -, hy⟩ | ⟨⟨hi1, -⟩, hi2, -⟩
      · subst hi hx hy; rfl
      · subst hi1; exact absurd hi2 (zmod5_add_one_add_one_ne i')
  -- count `S`
  let a : ZMod 5 → ℕ := fun i => ∑ x : Fin n, if f (i, x) = 0 then 1 else 0
  let b : ZMod 5 → ℕ := fun i => ∑ x : Fin n, if f (i, x) = 1 then 1 else 0
  have hab : ∀ i, a i + b i = n := by
    intro i
    simp only [a, b, ← Finset.sum_add_distrib, ite_add_fin2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hcard : S.card = ∑ i : ZMod 5, (a i * a (i + 1) + b i * b (i + 1)) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [a, b, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    exact ite_eq_fin2 _ _
  have hsum : ∑ i : ZMod 5, (a i * a (i + 1) + b i * b (i + 1)) =
      (a 0 * a 1 + b 0 * b 1) + (a 1 * a 2 + b 1 * b 2) + (a 2 * a 3 + b 2 * b 3) +
      (a 3 * a 4 + b 3 * b 4) + (a 4 * a 0 + b 4 * b 0) := by
    exact Fin.sum_univ_five (fun i : ZMod 5 => a i * a (i + 1) + b i * b (i + 1))
  calc n ^ 2 ≤ _ := c5_ineq n (a 0) (a 1) (a 2) (a 3) (a 4) (b 0) (b 1) (b 2) (b 3) (b 4)
          _hn (hab 0) (hab 1) (hab 2) (hab 3) (hab 4)
    _ = S.card := by rw [hcard, hsum]
    _ ≤ _ := hS

end Erdos23

