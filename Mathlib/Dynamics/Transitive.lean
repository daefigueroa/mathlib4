/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Perfect
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Order.Interval.Finset.Defs

/-!
# Point transitive action of a monoid

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

section

variable (M α : Type*) [TopologicalSpace α]

/-- An action of an additive monoid `M` on a topological space is called *point transitive* if
there exists a point `x : α ` with dense `M`-orbit. -/
class AddAction.IsPointTransitive [AddMonoid M] [AddAction M α] : Prop where
  exists_dense_orbit : ∃ x : α, Dense (AddAction.orbit M x)

/-- An action of a monoid `M` on a topological space is called *point transitive* if there exists a
point `x : α` with dense `M`-orbit. -/
@[to_additive]
class MulAction.IsPointTransitive [Monoid M] [MulAction M α] : Prop where
  exists_dense_orbit : ∃ x : α, Dense (orbit M x)

/-- An action of an additive monoid `M` on a topological space `α` is called
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m +ᵥ U ) ∩ V` is nonempty. -/
class AddAction.IsTopologicallyTransitive [AddMonoid M] [AddAction M α] : Prop where
  exists_smul_inter : ∀ {U : Set α}, IsOpen U → U.Nonempty → {V : Set α} → IsOpen V → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if
for any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that
`(m ⬝ U ) ∩ V` is nonempty. -/
@[to_additive]
class MulAction.IsTopologicallyTransitive [Monoid M] [MulAction M α] : Prop where
  exists_smul_inter : ∀ {U : Set α}, IsOpen U → U.Nonempty → {V : Set α} → IsOpen V → V.Nonempty →
    ∃ m : M, ((m • U) ∩ V).Nonempty

end

open MulAction Set

section

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [MulAction M α] [MulAction G α]

@[to_additive]
theorem MulAction.thmname1 {s : Set α} : (∀ c : M, c • s ⊆ s) ↔ ⋃ c : M, c • s ⊆ s := by simp

@[to_additive]
theorem MulAction.thmname2 {s : Set α} : (∀ c : M, c • s ⊆ s) ↔ ∀ c : M, s ⊆ (c • ·) ⁻¹' s := by
  simp only [← image_smul, image_subset_iff]

@[to_additive]
theorem MulAction.thmname3 {s : Set α} : (∀ c : M, c • s ⊆ s) ↔ ∀ c : M, (c • ·) ⁻¹' sᶜ ⊆ sᶜ := by
  simp only [thmname2, preimage_compl, compl_subset_compl]

@[to_additive]
theorem MulAction.thmname4 {s : Set α} :
  (⋃ c : M, (c • ·) ⁻¹' s ⊆ s) ↔ (∀ c : M, (c • ·) ⁻¹' s ⊆ s) := by simp

variable [TopologicalSpace α]

section IsPointTransitive

@[to_additive]
theorem MulAction.isPointTransitive.mk {x : α} (h : Dense (orbit M x)) :
    IsPointTransitive M α := by exact ⟨x, h⟩

/-- Given a monoid action on a topological space `α`, a point `x` is said to be *transitive* if the
-- orbit of `x` under `M` is dense in `α`. -/
@[to_additive]
abbrev MulAction.transitivePoints (M : Type*) (α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Set α := {x : α | Dense (orbit M x)}

@[to_additive]
theorem MulAction.mem_transitivePoints_iff (x : α) :
    x ∈ transitivePoints M α ↔ Dense (orbit M x) := by rfl

@[to_additive]
theorem MulAction.preimage_transitivePoints_subset (c : M) :
    (c • ·) ⁻¹' transitivePoints M α ⊆ transitivePoints M α := fun _ ↦ .mono (orbit_smul_subset ..)

@[to_additive]
theorem MulAction.mem_transitivePoints_of_smul {c : M} {x : α} (h : c • x ∈ transitivePoints M α) :
    x ∈ transitivePoints M α := preimage_subset_iff.1 (preimage_transitivePoints_subset M c) x h

@[to_additive]
theorem MulAction.exists_dense_orbit [IsPointTransitive M α] : ∃ x : α, Dense (orbit M x) :=
  IsPointTransitive.exists_dense_orbit

@[to_additive]
theorem MulAction.isPointTransitive_iff : IsPointTransitive M α ↔ Nonempty (transitivePoints M α) :=
  ⟨fun h ↦ by simp [transitivePoints, exists_dense_orbit M], fun hne ↦ ⟨nonempty_subtype.1 hne⟩⟩

@[to_additive]
theorem MulAction.mem_transitivePoints [IsMinimal M α] (x : α) : x ∈ transitivePoints M α :=
  dense_orbit M x

@[to_additive]
instance MulAction.instNonemptyTransitivePoints [IsPointTransitive M α] :
    Nonempty (transitivePoints M α) := (isPointTransitive_iff M).1 (by assumption)

@[to_additive]
theorem MulAction.isMinimal_iff_transitivePoints : IsMinimal M α ↔ transitivePoints M α = univ :=
  Iff.trans ⟨fun _ ↦ dense_orbit M, fun h ↦ ⟨h⟩⟩ (eq_univ_iff_forall).symm

@[to_additive]
theorem MulAction.smul_transitivePoints_eq (c : G) :
    c • transitivePoints G α = transitivePoints G α := by
  refine Set.ext fun x ↦ ⟨fun ⟨y, _, _⟩ ↦ by simp_all [← orbit_smul c y], ?_⟩
  exact fun _ ↦ mem_smul_set.2 ⟨c⁻¹ • x, by simpa⟩

@[to_additive]
theorem exists_denseRange_smul [IsPointTransitive M α] : ∃ x : α, DenseRange fun c : M ↦ c • x :=
  exists_dense_orbit M

@[to_additive]
instance MulAction.isPointTransitive_of_minimal [IsMinimal M α] [h : Nonempty α] :
    IsPointTransitive M α := (isPointTransitive_iff M).2 (h.elim fun x ↦ ⟨x, dense_orbit M x⟩)

@[to_additive]
theorem MulAction.exists_smul_mem [IsPointTransitive M α] :
    ∃ x : α, ∀ {U}, IsOpen U → U.Nonempty → ∃ c : M, c • x ∈ U :=
  (exists_denseRange_smul M).imp (fun _ g _ hUo hne ↦ DenseRange.exists_mem_open g hUo hne)

@[to_additive]
theorem MulAction.dense_of_smul_invariant_transitivePoints {s : Set α} (hs : ∀ c : M, c • s ⊆ s)
    (hx : ∃ x : α, x ∈ s ∧ Dense (MulAction.orbit M x)) : Dense s :=
  hx.elim fun x h₁ ↦ h₁.elim fun h₂ h₃ ↦ .mono (range_subset_iff.2 fun _ ↦ hs _ ⟨x, h₂, rfl⟩) h₃

@[to_additive]
theorem MulAction.univ_of_isClosed_smul_invariant_transitivePoint {s : Set α} (hc : IsClosed s)
    (hs : ∀ c : M, c • s ⊆ s) (hx : ∃ x : α, x ∈ s ∧ Dense (orbit M x)) : s = univ :=
  hc.closure_eq ▸ (dense_of_smul_invariant_transitivePoints M hs hx).closure_eq

end IsPointTransitive

section IsTopologicallyTransitive

@[to_additive]
theorem MulAction.exists_smul_inter [IsTopologicallyTransitive M α] {U : Set α} (h₁ : IsOpen U)
    (h₂ : U.Nonempty) {V : Set α} (h₃ : IsOpen V) (h₄ : V.Nonempty) :
    ∃ m : M, ((m • U) ∩ V).Nonempty := IsTopologicallyTransitive.exists_smul_inter h₁ h₂ h₃ h₄

@[to_additive]
theorem MulAction.IsTopologicallyTransitive_iff :
IsTopologicallyTransitive M α ↔ ∀ {U : Set α}, IsOpen U → U.Nonempty → {V : Set α} → IsOpen V →
V.Nonempty → ∃ m : M, ((m • U) ∩ V).Nonempty := ⟨(fun h => h.1), fun h => ⟨h⟩⟩

/-- A monoid action on `α` by `M` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union over the elements of `M` of images of `U` is dense in `α`. -/
@[to_additive]
theorem MulAction.isTopologicallyTransitive_iff_dense_image :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, m • U) := by
  simp [IsTopologicallyTransitive_iff, dense_iff_inter_open, inter_iUnion, inter_comm]

/-- A monoid action on `α` by `M` is topologically transitive if and only if for any nonempty open
subset `U` of `α` the union of the preimages of `U` over the elements of `M` is dense in `α`. -/
@[to_additive]
theorem MulAction.isTopologicallyTransitive_iff_dense_preimage :
    IsTopologicallyTransitive M α ↔
      ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, (m • ·) ⁻¹' U) := by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ ↦ h.1 h₃ h₄ h₁ h₂, fun h ↦ ⟨fun h₁ h₂ _ h₃ h₄ ↦ h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]
theorem IsOpen.dense_iUnion_smul [h : IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, m • U) :=
  (isTopologicallyTransitive_iff_dense_image M).1 h hUo hUne

@[to_additive]
theorem IsOpen.dense_iUnion_smul_preimage [h : IsTopologicallyTransitive M α]
    {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, (m • ·) ⁻¹' U) :=
  (isTopologicallyTransitive_iff_dense_preimage M).1 h hUo hUne

/-- Let `M` be a topologically transitive monoid action on `α`. If `U : Set α` is nonempty and
`(⋃ m : M, (m • ·) ⁻¹' U) ⊆ U` then `U` is dense in `α`. -/
@[to_additive]
theorem IsOpen.dense_of_smul_invariant [IsTopologicallyTransitive M α] {U : Set α} (hUo : IsOpen U)
    (hUne : U.Nonempty) (hUinv : (⋃ m : M, (m • ·) ⁻¹' U) ⊆ U) : Dense U :=
  .mono hUinv (hUo.dense_iUnion_smul_preimage M hUne)

/-- A continuous monoid action on `α` by `M` is topologically transitive if and only if any
nonempty open subset `U` of `α` with `(⋃ m : M, (m • ·) ⁻¹' U) ⊆ U` is dense in `α`. -/
@[to_additive]
theorem MulAction.isTopologicallyTransitive_iff_dense_of_invariant [ContinuousConstSMul M α] :
    IsTopologicallyTransitive M α ↔
      ∀ {U : Set α}, IsOpen U → U.Nonempty → ⋃ m : M, (m • ·) ⁻¹' U ⊆ U → Dense U := by
  refine ⟨fun a _ h h₁ h₂ ↦ h.dense_of_smul_invariant M h₁ h₂, fun h ↦ ?_⟩
  refine (isTopologicallyTransitive_iff_dense_preimage M).2 fun {U} hU _ ↦ ?_
  have hne : (⋃ m : M, (m • ·) ⁻¹' U).Nonempty := nonempty_iUnion.2 ⟨1, by simpa [one_smul]⟩
  refine h (isOpen_iUnion fun a ↦ (continuous_const_smul a).isOpen_preimage U hU) hne fun x hx ↦ ?_
  simp only [mem_iUnion, mem_preimage, ← smul_assoc] at ⊢ hx
  exact hx.elim (fun a h => h.elim (fun b hc => ⟨b • a, hc⟩))

@[to_additive]
instance MulAction.instIsTopologicallyTransitive_of_minimal [IsMinimal M α] :
    IsTopologicallyTransitive M α := by
  refine (isTopologicallyTransitive_iff_dense_preimage M).2 fun h hn ↦ ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

end IsTopologicallyTransitive

/-- If `α` is a nonempty Baire space with a second-countable topology, then any topologically
transitive monoid action on `α` that is continuous in the second argument is point transitive. -/
@[to_additive]
theorem MulAction.IsTopologicallyTransitive.IsPointTransitive_smul [Nonempty α] [BaireSpace α]
    [SecondCountableTopology α] [hc : ContinuousConstSMul M α] :
    IsTopologicallyTransitive M α → IsPointTransitive M α := by
  refine fun h ↦ ⟨match exists_countable_basis α with | ⟨b, h₁, h₂, h₃⟩ => ?_⟩
  suffices h : Dense (⋂ s ∈ b, ⋃ m, (m • ·) ⁻¹' s) by
    rcases Dense.nonempty (X := α) h with ⟨y, hy⟩
    simp [h₃.dense_iff, mem_iInter, inter_nonempty] at hy ⊢
    exact ⟨y, fun o h _ ↦ match hy _ h with | ⟨z, h⟩ => ⟨z • y, h, mem_orbit y z⟩⟩
  refine dense_biInter_of_isOpen ?_ h₁ fun s hs ↦ (h₃.isOpen hs).dense_iUnion_smul_preimage M ?_
  · exact fun o ↦ fun ho ↦ isOpen_iUnion fun m ↦ by simp [(h₃.isOpen ho).preimage (hc.1 m)]
  · exact s.nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h₂)

/-- A point transitive group action is topologically transitive -/
@[to_additive]
theorem MulAction.instIsTopologicallyTransitive [h : IsPointTransitive G α] :
    IsTopologicallyTransitive G α := by
  refine ⟨match h.exists_dense_orbit with | ⟨x, hx⟩ => fun ho hne V hVo hVne ↦ ?_⟩
  simp only [dense_iff_inter_open, inter_nonempty, mem_smul_set, exists_exists_and_eq_and] at hx ⊢
  obtain ⟨⟨y, h, a, ha⟩, ⟨_, _, b, hb⟩⟩ := And.intro (hx _ ho hne) (hx V hVo hVne)
  exact ⟨b • a⁻¹, y, ⟨h, by simpa only [smul_eq_mul, ← ha, ← mul_smul, inv_mul_cancel_right, hb]⟩⟩

end

variable (M : Type*) {α : Type*} [TopologicalSpace α]

/-- If `α` is a T1 space with no isolated points, and `M` is a commutative linearly ordered monoid
in which all intervals bounded above are finite and for all `a ≤ b` in `M` there is some `c` for
which `a * c = b`, then a point transitive action by M on `α` is topologically transitive. -/
@[to_additive]
theorem MulAction.IsPointTransitive.IsTopologicallyTransitive [CommMonoid M] [MulAction M α]
[LinearOrder M] [ExistsMulOfLE M] [LocallyFiniteOrderBot M] [T1Space α] [PerfectSpace α] :
    IsPointTransitive M α → IsTopologicallyTransitive M α := by
  refine fun ⟨x, hx⟩ ↦ ⟨fun {U} ho hne V hVo ⟨v, hv⟩ ↦ ?_⟩
  have ⟨y, h, hyo⟩ := dense_iff_inter_open.1 hx U ho hne
  have ⟨a, ha⟩  := mem_orbit_iff.1 hyo
  let I := Finset.Iic a
  let f : M → α := (· • x)
  have ho := hVo.sdiff (by simpa using isClosed_biUnion_finset (s := I) (f := fun i ↦ {f i}))
  have hn := ((infinite_of_mem_nhds v (hVo.mem_nhds hv)).diff (I.finite_toSet.image f)).nonempty
  have ⟨z, ⟨⟨_, hz⟩, b, hb⟩⟩ := dense_iff_inter_open.1 hx (V \ f '' I) (by rwa [image_eq_iUnion]) hn
  simp_all [mem_image, not_exists, not_and, imp_not_comm, Finset.mem_Iic, not_le, I]
  have ⟨c, _⟩ := exists_mul_of_le (hz b hb).le
  refine ⟨c, (c * a) • x, mem_smul_set.2 ⟨y, h, by rw [← ha, mul_smul]⟩, by simp_all [mul_comm]⟩
