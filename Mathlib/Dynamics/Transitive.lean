/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Perfect

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
  exists_nonempty_inter : ∀ {U V : Set α}, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that `(m ⬝ U ) ∩ V`
is nonempty. -/
@[to_additive]
class MulAction.IsTopologicallyTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  exists_nonempty_inter : ∀ {U V : Set α}, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ m : M, ((m • U) ∩ V).Nonempty

open MulAction Set

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

section IsPointTransitive

/-- Given a monoid action on a topological space `α`, a point `x` is said to be *transitive* if the
-- orbit of `x` under `M` is dense in `α`. -/
@[to_additive]
def MulAction.transitivePoints (M : Type*) (α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Set α := {x : α | Dense (orbit M x)}

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

end IsPointTransitive

section IsTopologicallyTransitive

@[to_additive]
theorem MulAction.exists_nonempty_inter [IsTopologicallyTransitive M α] {U V : Set α}
  (hUo : IsOpen U) (hVo : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    ∃ m : M, ((m • U) ∩ V).Nonempty :=
  MulAction.IsTopologicallyTransitive.exists_nonempty_inter hUo hVo hUne hVne

/-- A monoid action on `α` by `M` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union over the elements of `M` of images of `U` is dense in `α`. -/
@[to_additive]
theorem isTopologicallyTransitive_iff_dense_iUnion_smul :
    IsTopologicallyTransitive M α ↔
∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, m • U) := by
  simp [dense_iff_inter_open, inter_nonempty]
  constructor
  · refine (fun h U hoU hneU V hoV hneV ↦ ?_)
    obtain ⟨m, ⟨a,ha⟩⟩ := (h.exists_nonempty_inter hoU hoV hneU hneV)
    exact ⟨a, ⟨ha.right, ⟨m, ha.left⟩⟩⟩
  · intro h
    constructor
    intro U V hoU hoV hneU hneV
    obtain ⟨a, haV, m, haU⟩ := h hoU hneU V hoV hneV
    exact ⟨m, a, haU, haV⟩

/-- A monoid action on `α` by `M` is topologically transitive if and only if for any nonempty open
subset `U` of `α` the union of the preimages of `U` over the elements of `M` is dense in `α`. -/
@[to_additive]
theorem isTopologicallyTransitive_iff_dense_preimage_smul :
    IsTopologicallyTransitive M α ↔
      ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, (m • ·) ⁻¹' U) := by
  constructor
  · intro h U hUo hUne
    haveI := h
    simp only [dense_iff_inter_open]
    intro V hVo hVne
    simp only [inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff, image_smul]
    exact exists_nonempty_inter M hVo hUo hVne hUne
  · intro h
    constructor
    intro U V hUo hVo hUne hVne
    have hden : Dense (⋃ m : M, (fun x : α => m • x) ⁻¹' V) := h hVo hVne
    rcases (dense_iff_inter_open.mp hden) U hUo hUne with ⟨x, hxU, hxUnion⟩
    rcases mem_iUnion.mp hxUnion with ⟨m, hxPre⟩
    refine ⟨m, ?_⟩
    refine ⟨m • x, ?_⟩
    constructor
    · exact ⟨x, hxU, rfl⟩
    · exact hxPre

/-- Given a topologically transitive monoid action on `α` by `M`, the union of the preimages of a
nonempty open set over the elements of `M` is dense in `α`. -/
@[to_additive]
theorem IsOpen.dense_iUnion_preimage_smul [IsTopologicallyTransitive M α]
    {U : Set α} (hUne : U.Nonempty) (hUo : IsOpen U) : Dense (⋃ m : M, (m • ·) ⁻¹' U) :=
  (isTopologicallyTransitive_iff_dense_preimage_smul M).mp
    (inferInstance : IsTopologicallyTransitive M α) hUo hUne

/-- Let `M` be a topologically transitive monoid action on `α`. If `U : Set α` is nonempty and for
all `m : M` the preimage of `U` under `x ↦ m • x` is contained in `U` then the image of `U` under
the action by `M` is dense in `α`. -/
@[to_additive]
theorem MulAction.thmname1 [IsTopologicallyTransitive M α] {U : Set α} (hU : U.Nonempty)
    (hneg : ∀ m : M, (fun x : α => m • x) ⁻¹' U ⊆ U) : Dense (⋃ m : M, m • U) := by
  rw [← Set.compl_ne_univ] at hU
  sorry

/-- A monoid action on `α` is topologically transitive if and only if every proper closed invariant
subset of `α` has empty interior. -/
@[to_additive]
theorem isTopologicallyTransitive_iff_empty_interior_of_isClosed_invariant_smul :
    IsTopologicallyTransitive M α ↔ ∀ {s : Set α}, IsClosed s → (∀ m : M, m • s ⊆ s) →
      s ≠ (Set.univ : Set α) → interior s = ∅ := by
  constructor
  · intro h U hcU hU hn
    refine interior_eq_empty_iff_dense_compl.mpr ?_
    simp_all [← Set.nonempty_compl]
    have g := IsClosed.isOpen_compl (s := U)
    -- exact (isTopologicallyTransitive_iff_dense_iUnion_smul M).mp h g hn
    sorry
  · sorry

end IsTopologicallyTransitive

/-- If `α` is a nonempty Baire space with a second-countable topology, then any topologically
transitive monoid action on `α` that is continuous in the second argument is point transitive. -/
@[to_additive]
theorem MulAction.IsTopologicallyTransitive.IsPointTransitive_smul₁ [Nonempty α] [BaireSpace α]
    [SecondCountableTopology α] [ContinuousConstSMul M α] :
    IsTopologicallyTransitive M α → IsPointTransitive M α := by
  obtain ⟨b, hbc, hbne, hbb⟩ := exists_countable_basis α
  refine fun h ↦ ⟨?_⟩
  simp [IsTopologicalBasis.dense_iff hbb]
  suffices h : Dense (⋂ A : b, ⋃ m : M, (fun x : α => m • x) ⁻¹' (A : Set α)) by
    rcases Dense.nonempty h with ⟨y, hy⟩
    use y
    intro o ho hone
    simp [mem_iInter] at hy
    have hyz := hy o ho
    refine inter_nonempty.mpr ?_
    rcases hyz with ⟨z, hz⟩
    exact ⟨z • y, ⟨hz, by simp [mem_orbit]⟩⟩
  simp [iInter_subtype]
  refine dense_biInter_of_isOpen ?_ hbc ?_
  · refine fun o => ?_
    intro ho
    have hoo := hbb.isOpen ho
    refine isOpen_iUnion ?_
    exact fun m ↦ by simp [hoo.preimage (continuous_const_smul m)]
  · intro s hs
    have h₂ : s.Nonempty := s.nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs hbne)
    refine (IsOpen.dense_iUnion_preimage_smul M) h₂ (hbb.isOpen hs)

-- [h : ∀ x : α, NeBot (𝓝[≠] x)]

/-- If `α` is a T1 space with no isolated points, then a point transitive monoid action on `α` that
is continuous in the second argument is topologically transitive. -/
@[to_additive]
theorem MulAction.IsPointTransitive.IsTopologicallyTransitive [T1Space α] [PerfectSpace α] :
    IsPointTransitive M α → IsTopologicallyTransitive M α := by
  intro h
  obtain ⟨x, hx⟩ := h.exists_dense_orbit
  refine ⟨fun hUo hVo hUne hVne ↦ ?_⟩
  have hUx := dense_iff_inter_open.mp hx _ hUo hUne
  sorry

/-- A point transitive group action is topologically transitive -/
@[to_additive]
theorem instIsPointTransitive_of_group_smul [IsTopologicallyTransitive G α] :
    IsPointTransitive G α := by sorry
