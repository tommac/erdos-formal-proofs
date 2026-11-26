import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Data.Sym.Sym2

/-! Erdős 1171 — `mono_k`. Definition copied verbatim from
`FormalConjecturesForMathlib/SetTheory/Ordinal/PartitionRelation.lean`. -/

open Cardinal Ordinal

universe u

def OrdinalMultiColorRamsey (α β : Ordinal.{u}) (γ : Cardinal.{u}) (k : ℕ) : Prop :=
  ∀ col : Sym2 α.ToType → Fin (k + 1),
    (∃ A : Set α.ToType,
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = 0) ∧
      typeLT A = β) ∨
    (∃ (i : Fin k) (A : Set α.ToType),
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = i.succ) ∧
      #A = γ)

namespace Erdos1171

/-- General monotonicity: fewer small colours is easier, as long as the small-colour
target `γ` has at least two elements (so a monochromatic witness contains an edge). -/
theorem mono_k_general {α β : Ordinal.{u}} {γ : Cardinal.{u}} (hγ : 1 < γ)
    {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey α β γ k) :
    OrdinalMultiColorRamsey α β γ j := by
  intro col
  rcases hk (fun e => Fin.castLE (by omega) (col e)) with
    ⟨A, hA, hty⟩ | ⟨i, A, hA, hcard⟩
  · refine Or.inl ⟨A, fun x hx y hy hxy => ?_, hty⟩
    have h := congrArg Fin.val (hA x hx y hy hxy)
    exact Fin.ext (by simpa using h)
  · -- `A` has two distinct points, so the colour `i.succ` is actually hit by `col`.
    have hnt : A.Nontrivial := by
      by_contra hsub
      rw [Set.not_nontrivial_iff] at hsub
      have := (Cardinal.mk_le_one_iff_set_subsingleton).2 hsub
      rw [hcard] at this
      exact absurd hγ (not_lt.2 this)
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hval := congrArg Fin.val (hA x hx y hy hxy)
    simp only [Fin.val_castLE, Fin.val_succ] at hval
    have hij : (i : ℕ) < j := by
      have := (col s(x, y)).isLt
      omega
    refine Or.inr ⟨⟨i, hij⟩, A, fun x' hx' y' hy' hxy' => ?_, hcard⟩
    have h := congrArg Fin.val (hA x' hx' y' hy' hxy')
    simp only [Fin.val_castLE, Fin.val_succ] at h
    exact Fin.ext (by simpa [Fin.val_succ] using h)

/-- Universe transfer: the partition relation only depends on the ordinals/cardinal up to
`lift`, because order-isomorphic index types carry colourings and witnesses across. -/
theorem transfer.{v} {α β : Ordinal.{u}} {γ : Cardinal.{u}} {α' β' : Ordinal.{v}}
    {γ' : Cardinal.{v}} (hα : Ordinal.lift.{v} α = Ordinal.lift.{u} α')
    (hβ : Ordinal.lift.{v} β = Ordinal.lift.{u} β')
    (hγ : Cardinal.lift.{v} γ = Cardinal.lift.{u} γ') {k : ℕ}
    (h : OrdinalMultiColorRamsey α β γ k) : OrdinalMultiColorRamsey α' β' γ' k := by
  have hiso : Nonempty ((· < · : α.ToType → α.ToType → Prop) ≃r
      (· < · : α'.ToType → α'.ToType → Prop)) := by
    rw [← Ordinal.lift_type_eq.{u, v, 0}, Ordinal.type_toType, Ordinal.type_toType]
    exact hα
  obtain ⟨e⟩ := hiso
  -- `A` and `e '' A` are order-isomorphic
  let img : ∀ A : Set α.ToType, A ≃ (e '' A) := fun A => Equiv.Set.image e A e.injective
  have himg : ∀ A : Set α.ToType,
      Nonempty ((· < · : A → A → Prop) ≃r (· < · : (e '' A) → (e '' A) → Prop)) :=
    fun A => ⟨⟨img A, fun {a b} => by
      change e a.1 < e b.1 ↔ a.1 < b.1
      exact e.map_rel_iff⟩⟩
  intro col'
  rcases h (fun s => col' (Sym2.map e s)) with ⟨A, hA, hty⟩ | ⟨i, A, hA, hcard⟩
  · refine Or.inl ⟨e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have := hA x hx y hy (fun h => hxy (by rw [h]))
      simpa [Sym2.map_mk] using this
    · apply Ordinal.lift_inj.{u}.1
      rw [← hβ, ← hty]
      exact (Ordinal.lift_type_eq.{u, v, 0}.2 (himg A)).symm
  · refine Or.inr ⟨i, e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have := hA x hx y hy (fun h => hxy (by rw [h]))
      simpa [Sym2.map_mk] using this
    · have h' : Cardinal.lift.{u} #(e '' A) = Cardinal.lift.{u} γ' := by
        rw [← hγ, ← hcard]
        exact (Cardinal.lift_mk_eq'.2 ⟨img A⟩).symm
      exact Cardinal.lift_inj.1 h'

/-- The formal-conjectures target `Erdos1171.erdos_1171.variants.mono_k`, with the same
(independent) universe levels Lean assigns to the repo statement. -/
theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  refine mono_k_general (by norm_num) hjk (transfer ?_ ?_ ?_ hk)
  · simp only [pow_two, Ordinal.lift_mul, Ordinal.lift_omega, Ordinal.lift_one]
  · simp only [Ordinal.lift_mul, Ordinal.lift_omega, Ordinal.lift_one, Ordinal.lift_omega0]
  · simp only [Cardinal.lift_ofNat]

end Erdos1171

