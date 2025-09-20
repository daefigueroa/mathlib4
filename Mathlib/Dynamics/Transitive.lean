/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
import Mathlib.Dynamics.Minimal

/-!
# Point transitive action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be
*point transitive* if there exists a point in `α` with dense `M`-orbit. We also provide an
additive version of this definition and prove some basic facts about point transitive
actions.

## TODO

* Define the set of transitive points

## Tags

group action, point transitive
-/


open Pointwise TopologicalSpace Filter
open scoped Topology

/-- An action of an additive monoid `M` on a topological space is called *point transitive* if there
exists a point `x : α ` with dense `M`-orbit. -/
class AddAction.IsPointTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where exists_dense_orbit : ∃ x : α, Dense (AddAction.orbit M x)

/-- An action of a monoid `M` on a topological space is called *point transitive* if there exists a
point `x : α` with dense `M`-orbit. -/
@[to_additive]
class MulAction.IsPointTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  exists_dense_orbit : ∃ x : α, Dense (MulAction.orbit M x)

/-- An action of an additive monoid `M` on a topological space `α` is called
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m +ᵥ U ) ∩ V` is nonempty. -/
class AddAction.IsTopologicallyTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α]
    [AddAction M α] : Prop where
  nonempty_inter : ∀ {U V : Set α}, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that `(m ⬝ U ) ∩ V`
is nonempty. -/
@[to_additive]
class MulAction.IsTopologicallyTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  nonempty_inter : ∀ ⦃U V : Set α⦄, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ m : M, ((m • U) ∩ V).Nonempty

open MulAction Set

/-- Given a monoid action on a topological space `α`, a point `x` is said to be *transitive* if the
-- orbit of `x` under `M` is dense in `α`. -/
@[to_additive]
def MulAction.transitivePoints (M : Type*) (α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Set α := {x : α | Dense (orbit M x)}

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

/-- A monoid action on `α` is topologically transitive if and only if the image of any non-empty
open subset of `α` is dense in `α`. -/
@[to_additive]
theorem isTopologicallyTransitive_iff_dense_iUnion_smul_of_isOpen_nonempty :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, m • U) := by
  constructor
  simp [dense_iff_inter_open]
  refine (fun h U hoU hneU V hoV hneV ↦ ?_)
  #check (h.nonempty_inter hoU hoV hneU hneV)
  simp [h.nonempty_inter hoU hoV hneU hneV]

/-- A monoid action on `α` is topologically transitive if and only if every proper closed invariant
subset of `α` has empty interior. -/
@[to_additive]
theorem isTopologicallyTransitive_iff_empty_interior_of_isClosed_invariant_smul :
    IsTopologicallyTransitive M α ↔ ∀ {s : Set α}, IsClosed s → (∀ m : M, m • s ⊆ s) →
      s ≠ (Set.univ : Set α) → interior s = ∅ :=
  sorry

/-- If `α` has no isolated points, then any point transitive monoid action on `α` is topologically
transitive. -/
@[to_additive]
theorem MulAction.IsPointTransitive.IsTopologicallyTransitive [h : ∀ x : α, NeBot (𝓝[≠] x)] :
    IsPointTransitive M α → IsTopologicallyTransitive M α :=
  sorry

/-- If `α` is a separable Baire space, then any topologically transitive monoid action on `α` is
point transitive. -/
@[to_additive]
theorem MulAction.IsTopologicallyTransitive.IsPointTransitive_smul [SeparableSpace α]
    [BaireSpace α] : IsTopologicallyTransitive M α → IsPointTransitive M α :=
  sorry

/-- A point transitive group action is topologically transitive -/
@[to_additive]
theorem thmname2_smul : IsPointTransitive G α → IsTopologicallyTransitive G α := sorry

@[to_additive]
theorem MulAction.mem_transitivePoints_iff (x : α) :
    x ∈ transitivePoints M α ↔ Dense (orbit M x) := by rfl

@[to_additive]
theorem MulAction.exists_dense_orbit [IsPointTransitive M α] : ∃ x : α, Dense (orbit M x) :=
  MulAction.IsPointTransitive.exists_dense_orbit

@[to_additive]
theorem MulAction.isPointTransitive_iff : IsPointTransitive M α ↔ Nonempty (transitivePoints M α) :=
  ⟨fun h ↦ by simp [transitivePoints, exists_dense_orbit M], fun hne ↦ ⟨nonempty_subtype.mp hne⟩⟩

@[to_additive]
instance MulAction.instNonemptyTransitivePoints [IsPointTransitive M α] :
    Nonempty (transitivePoints M α) := (MulAction.isPointTransitive_iff M).mp (by assumption)

@[to_additive]
theorem MulAction.mem_transitivePoints [IsMinimal M α] (x : α) : x ∈ transitivePoints M α :=
  dense_orbit M x

@[to_additive]
theorem MulAction.isMinimal_iff_univ : IsMinimal M α ↔ transitivePoints M α = univ :=
  Iff.trans ⟨fun _ ↦ dense_orbit M, fun h ↦ ⟨h⟩⟩ (eq_univ_iff_forall).symm

@[to_additive]
theorem MulAction.transitivePoints_smul :
    ∀ c : G, transitivePoints G α = c • transitivePoints G α := by
  intro c
  unfold transitivePoints
  ext x
  constructor
  · intro h
    refine mem_smul_set.mpr ?_
    use c⁻¹ • x
    simpa only [mem_setOf_eq, orbit_smul, smul_inv_smul, and_true]
  · intro h
    rcases h with ⟨y, hy, hyx⟩
    simp_all only [mem_setOf_eq, ← orbit_smul c y]

@[to_additive]
theorem exists_denseRange_smul [IsPointTransitive M α] : ∃ x : α, DenseRange fun c : M ↦ c • x :=
  MulAction.exists_dense_orbit M

@[to_additive]
instance (priority := 100) MulAction.isPointTransitive_of_minimal [IsMinimal M α] [Nonempty α] :
    IsPointTransitive M α :=
  (isPointTransitive_iff M).mpr ((inferInstance : Nonempty α).elim fun x ↦ ⟨x, dense_orbit M x⟩)

@[to_additive]
instance (priority := 100) MulAction.isPointTransitive_of_transitive [IsPretransitive M α]
    [Nonempty α] : IsPointTransitive M α := isPointTransitive_of_minimal M

@[to_additive]
theorem exists_smul_mem [IsPointTransitive M α] :
    ∃ x : α, ∀ {U}, IsOpen U → U.Nonempty → ∃ c : M, c • x ∈ U :=
  (exists_denseRange_smul M).imp (fun _ g _ hUo hne ↦ DenseRange.exists_mem_open g hUo hne)

@[to_additive]
theorem dense_of_smul_invariant_transitivePoint {s : Set α} (hs : ∀ c : M, c • s ⊆ s)
    (hx : ∃ x : α, x ∈ s ∧ Dense (MulAction.orbit M x)) : Dense s := by
  rcases hx with ⟨x, hxs, hxd⟩
  exact Dense.mono (Set.range_subset_iff.mpr (fun c ↦ hs c ⟨x, hxs, rfl⟩)) hxd

@[to_additive]
theorem univ_of_isClosed_smul_invariant_transitivePoint {s : Set α} (hc : IsClosed s)
    (hs : ∀ c : M, c • s ⊆ s) (hx : ∃ x : α, x ∈ s ∧ Dense (MulAction.orbit M x)) : s = univ :=
  hc.closure_eq ▸ (dense_of_smul_invariant_transitivePoint M hs hx).closure_eq
