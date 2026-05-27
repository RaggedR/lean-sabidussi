/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Group actions on simple graphs

Given a group `G` acting on a type `V` via `MulAction G V`, and a simple graph `Γ : SimpleGraph V`,
we say the action is a *graph action* if it preserves adjacency: `Γ.Adj u v → Γ.Adj (g • u) (g • v)`
for all `g : G`.

## Main definitions

* `GraphAction G Γ` — the action of `G` on `V` preserves the adjacency relation of `Γ`
* `GraphAction.adj_smul_iff` — for groups, adjacency is an iff (not just an implication)
* `GraphAction.toIso` — each `g : G` induces a graph isomorphism `Γ ≃g Γ`
* `IsVertexTransitive G Γ` — the action is a graph action and is transitive
* `IsArcTransitive G Γ` — the action is transitive on ordered adjacent pairs

## Main results

* `isArcTransitive_of_vertexTransitive_locallyTransitive` — vertex-transitive + locally
  transitive implies arc-transitive

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798, Chapter 1 §§3–5.
-/

variable {G V : Type*}

/-- A group action on `V` is a *graph action* on `Γ : SimpleGraph V` if it preserves adjacency. -/
class GraphAction (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop where
  /-- The action preserves adjacency. -/
  adj_smul : ∀ (g : G) (u v : V), Γ.Adj u v → Γ.Adj (g • u) (g • v)

namespace GraphAction

variable [Group G] [MulAction G V] {Γ : SimpleGraph V} [GraphAction G V Γ]

/-- For group actions, adjacency is preserved in both directions:
`Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v`. -/
theorem adj_smul_iff (g : G) (u v : V) : Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v := by
  constructor
  · intro h
    have h' := adj_smul g⁻¹ (g • u) (g • v) h
    simp only [inv_smul_smul] at h'
    exact h'
  · exact adj_smul g u v

/-- Each group element `g` induces a graph isomorphism `Γ ≃g Γ`. -/
noncomputable def toIso (g : G) : Γ ≃g Γ where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := adj_smul_iff g _ _

@[simp]
theorem toIso_apply (g : G) (v : V) : (toIso g : Γ ≃g Γ) v = g • v := rfl

@[simp]
theorem toIso_symm (g : G) : (toIso g : Γ ≃g Γ).symm = toIso g⁻¹ := by
  ext v
  simp [toIso]

theorem toIso_mul (g h : G) :
    (toIso (g * h) : Γ ≃g Γ) = (toIso h : Γ ≃g Γ).trans (toIso g) := by
  ext v
  simp [toIso, mul_smul]

end GraphAction

/-- A graph `Γ` is *vertex-transitive* under the action of `G` if `G` preserves adjacency
and acts transitively on the vertices. -/
class IsVertexTransitive (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop extends GraphAction G V Γ where
  /-- The action is transitive on vertices. -/
  pretransitive : MulAction.IsPretransitive G V

attribute [instance] IsVertexTransitive.pretransitive

/-- A graph `Γ` is *arc-transitive* under the action of `G` if for any two arcs
`(u₁, v₁)` and `(u₂, v₂)`, there exists `g ∈ G` sending `u₁ ↦ u₂` and `v₁ ↦ v₂`. -/
class IsArcTransitive (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop extends GraphAction G V Γ where
  /-- The action is transitive on arcs (ordered adjacent pairs). -/
  arc_transitive : ∀ u₁ v₁ u₂ v₂ : V, Γ.Adj u₁ v₁ → Γ.Adj u₂ v₂ →
    ∃ g : G, g • u₁ = u₂ ∧ g • v₁ = v₂

namespace IsArcTransitive

variable [Group G] [MulAction G V] {Γ : SimpleGraph V} [IsArcTransitive G V Γ]

/-- An arc-transitive graph with no isolated vertices is vertex-transitive.
The no-isolated-vertices condition is necessary: an edgeless graph is
arc-transitive vacuously but not vertex-transitive (unless |V| ≤ 1). -/
theorem isVertexTransitive (hne : ∀ v : V, ∃ w : V, Γ.Adj v w) :
    IsVertexTransitive G V Γ where
  pretransitive := ⟨by
    intro x y
    -- Every vertex has a neighbor, so pick arcs at x and y
    obtain ⟨x', hx'⟩ := hne x
    obtain ⟨y', hy'⟩ := hne y
    -- Arc-transitivity gives g sending (x, x') to (y, y')
    obtain ⟨g, hg, _⟩ := @arc_transitive G V _ _ Γ _ x x' y y' hx' hy'
    exact ⟨g, hg⟩⟩

end IsArcTransitive

/-- A graph is *locally transitive* at `v` if the stabilizer of `v` acts transitively
on the neighbors of `v`. -/
def IsLocallyTransitive (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) (v : V) : Prop :=
  ∀ w₁ w₂ : V, Γ.Adj v w₁ → Γ.Adj v w₂ →
    ∃ g : G, g • v = v ∧ g • w₁ = w₂

/-- A vertex-transitive, locally transitive graph is arc-transitive.
This is the characterization from background.tex: symmetric = vertex-transitive + locally
transitive. -/
theorem isArcTransitive_of_vertexTransitive_locallyTransitive
    [Group G] [MulAction G V] (Γ : SimpleGraph V) [IsVertexTransitive G V Γ]
    (hlocal : ∀ v : V, IsLocallyTransitive G V Γ v) :
    IsArcTransitive G V Γ where
  arc_transitive := by
    intro u₁ v₁ u₂ v₂ h₁ h₂
    -- Step 1: by vertex-transitivity, find g sending u₁ to u₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G u₁ u₂
    -- Step 2: g • v₁ is a neighbor of u₂ = g • u₁
    have hadj : Γ.Adj u₂ (g • v₁) := by
      rw [← hg]
      exact GraphAction.adj_smul g u₁ v₁ h₁
    -- Step 3: by local transitivity at u₂, find h fixing u₂ and sending g • v₁ to v₂
    obtain ⟨h, hhu₂, hhv⟩ := hlocal u₂ (g • v₁) v₂ hadj h₂
    -- Step 4: h * g does both
    exact ⟨h * g, by rw [mul_smul, hg, hhu₂], by rw [mul_smul, hhv]⟩
