# Sabidussi Formalization — Plan

## Goal

Formalize the core results of Robin Langer's honours thesis
*"Symmetric Graphs and their Quotients"* (arXiv:1306.4798) in Lean 4,
connecting Mathlib's group action machinery to its `SimpleGraph` library.

The headline theorem: **every symmetric (arc-transitive) graph is isomorphic
to a Sabidussi coset graph `Sab(G, H, HaH)`** for some group `G`, vertex
stabilizer `H`, and involution `a ∈ G \ H`.

---

## Where to Start Reading

### `reference/coset.tex` — the core chapter

This is the file that contains everything we need to formalize. It has four
sections, each mapping to a Lean module:

| Section | Key result | Lean module |
|---------|-----------|-------------|
| §1 Transitive Permutation Groups | Every transitive action ≅ coset action `(G, G⧸H)` | `CosetAction.lean` |
| §2 Sabidussi's Construction | Sabidussi graphs are vertex-transitive; every VT graph is a Sabidussi graph | `CosetGraph.lean` |
| §3 Group-Theoretic Characterization | Orbitals ↔ double cosets; symmetric graphs = `Sab(G, H, HaH)` with `a² = 1` | `Symmetric.lean` |
| §4 Quotient Graphs | Quotients of `Sab(G, H, HaH)` are `Sab(G, K, KaK)` for `H ≤ K ≤ G` | `Quotient.lean` |

### `reference/background.tex` — definitions only

Chapter 1 defines permutation groups, graphs, automorphisms, vertex-transitive
graphs, symmetric graphs, orbital graphs, blocks of imprimitivity, and
quotient graphs. Almost all of this is already in Mathlib (see inventory
below). Read it for notation, but don't formalize it — use Mathlib's versions.

### `reference/geometric.tex` — future work

The extension problem (unfolding a quotient back to the original graph) via
Gardiner–Praeger's induced bipartite graphs. This is the deeper part of the
thesis and a stretch goal.

---

## What Mathlib Already Has

### Graph theory (`Mathlib.Combinatorics.SimpleGraph`)
- `SimpleGraph V` — irreflexive symmetric relation on `V`
- `SimpleGraph.Hom`, `Embedding`, `Iso` — graph morphisms
- `SimpleGraph.mulCayley s` — Cayley graph (right-multiplication)
- `SimpleGraph.neighborSet`, `degree`, `edgeSet`
- Connectivity, coloring, matching, regularity — all present

### Group actions (`Mathlib.GroupTheory.GroupAction`)
- `MulAction.orbit`, `stabilizer`, `fixedPoints`, `fixedBy`
- **`MulAction.orbitEquivQuotientStabilizer`** — the orbit-stabilizer bijection `orbit G b ≃ G ⧸ stabilizer G b`
- **`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`** — the counting theorem
- `MulAction.IsPretransitive` — transitive action
- `MulAction.isPretransitive_quotient G H` — G acts transitively on G⧸H
- `MulAction.QuotientAction` — descended action on quotient
- **`MulAction.IsBlock`** — blocks of imprimitivity, with full theory
- **`MulAction.IsPreprimitive`** — primitive actions
- `MulAction.IsMultiplyPretransitive` — k-fold transitivity

### Cosets and quotients (`Mathlib.GroupTheory`)
- `Subgroup.leftCoset`, `rightCoset`, coset equivalence relations
- **`QuotientGroup`** — `G ⧸ N` for normal `N`, isomorphism theorems
- `Subgroup.normalCore` — ⋂ₓ x⁻¹Hx, the largest normal subgroup in H
- **`DoubleCoset`** — `H\G/K` with full partition theory, `doubleCoset a H K = H * {a} * K`

### Schreier graphs (`Mathlib.Combinatorics.Quiver.Schreier`)
- Schreier graphs as directed labeled *quivers* (NOT `SimpleGraph`)
- `SchreierGraph.labelling_isCovering` — covering map theory
- Note: Cayley graph = Schreier graph of left multiplication on `G` itself

---

## What Mathlib Does NOT Have (the gap we fill)

1. **No group action on `SimpleGraph`** — no `MulAction G V` preserving `Adj`
2. **No vertex-transitivity predicate for graphs** — `IsPretransitive` exists for abstract actions but isn't connected to `SimpleGraph`
3. **No coset graph as `SimpleGraph`** — Schreier graphs are quivers, `mulCayley` doesn't generalize to non-trivial stabilizers
4. **No Sabidussi representation theorem**
5. **No connection** between `DoubleCoset` and graph adjacency
6. **No quotient graph** construction as `SimpleGraph`

---

## Module Plan

### Module 1: `Sabidussi/GraphAction.lean` (~150 lines)

**Purpose**: Connect `MulAction` to `SimpleGraph`.

```
-- A group action on V that preserves adjacency
class GraphAction (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop where
  adj_smul : ∀ (g : G) (u v : V), Γ.Adj u v → Γ.Adj (g • u) (g • v)

-- Vertex-transitivity = IsPretransitive + GraphAction
def IsVertexTransitive (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop :=
  GraphAction G V Γ ∧ MulAction.IsPretransitive G V

-- Arc-transitivity = transitive on ordered adjacent pairs
def IsArcTransitive (G : Type*) (V : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : V, Γ.Adj u₁ v₁ → Γ.Adj u₂ v₂ →
    ∃ g : G, g • u₁ = u₂ ∧ g • v₁ = v₂

-- Key lemma: arc-transitive ↔ vertex-transitive + locally transitive
-- (Thesis: background.tex, Proposition after Definition 7)
theorem arcTransitive_iff_vertexTransitive_and_locallyTransitive ...
```

**Mathlib deps**: `MulAction`, `IsPretransitive`, `SimpleGraph.Basic`

**Thesis ref**: `background.tex` §§3–5

### Module 2: `Sabidussi/CosetGraph.lean` (~300 lines)

**Purpose**: Define the Sabidussi coset graph and prove basic properties.

```
-- The coset graph: vertices are G⧸H, adjacent when xy⁻¹ ∈ D
-- (Thesis: coset.tex, Definition after "Sabidussi Graph")
noncomputable def SimpleGraph.cosetGraph (G : Type*) [Group G]
    (H : Subgroup G) (D : Set G) (hD_symm : D = D⁻¹)
    (hD_disj : Disjoint D ↑H) : SimpleGraph (G ⧸ H) where
  Adj := Quotient.lift₂ (fun x y => xy⁻¹ ∈ D) ...
  symm := ... -- uses D = D⁻¹
  loopFree := ... -- uses D ∩ H = ∅

-- Cayley graph is a coset graph with H = ⊥
-- (Thesis: coset.tex, Definition "Cayley Graph")
theorem mulCayley_eq_cosetGraph_bot ...

-- G acts on G⧸H preserving cosetGraph adjacency
-- (Thesis: coset.tex, first half of Proposition "Sabidussi")
instance cosetGraph_graphAction ...

-- The coset graph is vertex-transitive
-- (immediate from isPretransitive_quotient + cosetGraph_graphAction)
theorem cosetGraph_isVertexTransitive ...

-- Valency of Sab(G, H, HaH) = |H| / |a⁻¹Ha ∩ H|
-- (Thesis: coset.tex, last Proposition of §3)
theorem cosetGraph_degree ...
```

**Mathlib deps**: `QuotientGroup`, `DoubleCoset`, `Quotient.lift₂`, `SimpleGraph.Basic`

**Thesis ref**: `coset.tex` §2 (Definitions + first half of Proposition)

### Module 3: `Sabidussi/Representation.lean` (~400 lines)

**Purpose**: The main theorem — every vertex-transitive graph is a coset graph.

```
-- The orbit-stabilizer map V → G ⧸ stabilizer(v) is a graph isomorphism
-- to the coset graph Sab(G, Gᵥ, D) where D is determined by the neighborhood
-- (Thesis: coset.tex, second half of Proposition "Sabidussi")
noncomputable def sabidussiIso [GraphAction G V Γ] [IsPretransitive G V]
    (v : V) : Γ ≃g cosetGraph G (stabilizer G v) D ...

-- The isomorphism is G-equivariant
theorem sabidussiIso_equivariant ...
```

**Key proof idea**: The orbit-stabilizer equivalence
`MulAction.orbitEquivQuotientStabilizer` gives `V ≃ G ⧸ Gᵥ` (since the action
is transitive, `orbit G v = univ`). The proof then shows this equivalence
transports adjacency: `Γ.Adj u w ↔ (representative of u) * (representative of w)⁻¹ ∈ D`,
where `D` is the union of cosets forming the neighborhood of `v`.

**Mathlib deps**: `orbitEquivQuotientStabilizer`, Module 1, Module 2

**Thesis ref**: `coset.tex` §2 (second half of Proposition "Sabidussi")

### Module 4: `Sabidussi/Symmetric.lean` (~350 lines)

**Purpose**: The characterization of symmetric graphs via double cosets and involutions.

```
-- Orbitals of (G, G⧸H) biject with double cosets H\G/H
-- (Thesis: coset.tex, Proposition "Lorimer" in §3)
def orbital_doubleCoset_equiv ...

-- Self-paired orbitals correspond to double cosets containing an involution
-- (Thesis: coset.tex, second part of Proposition "Lorimer" in §3)
theorem selfPaired_iff_contains_involution ...

-- Lorimer's Theorem: Sab(G, H, HaH) is G-symmetric when a² = 1, a ∉ H.
-- Every symmetric graph is of this form.
-- (Thesis: coset.tex, Theorem "Lorimer")
theorem lorimer_symmetric (a : G) (ha_inv : a ^ 2 = 1) (ha_notmem : a ∉ H) :
    IsArcTransitive G (G ⧸ H) (cosetGraph G H (↑(DoubleCoset.mk H a H)) ...) ...

theorem symmetric_is_sabidussi [IsArcTransitive G V Γ] :
    ∃ H : Subgroup G, ∃ a : G, a ^ 2 = 1 ∧ a ∉ H ∧
      Γ ≃g cosetGraph G H (↑(DoubleCoset.mk H a H)) ...
```

**Mathlib deps**: `DoubleCoset`, `orbitRel`, Modules 1–3

**Thesis ref**: `coset.tex` §3 (both Lorimer results)

### Module 5: `Sabidussi/Quotient.lean` (~250 lines) — stretch goal

**Purpose**: Quotients of Sabidussi graphs are Sabidussi graphs.

```
-- Lorimer's quotient theorem: if Γ ≅ Sab(G,H,HaH) and Σ is a quotient,
-- then Σ ≅ Sab(G,K,KaK) for some H ≤ K ≤ G.
-- (Thesis: coset.tex, Theorem in §4)
-- This connects to the block-subgroup correspondence (IsBlock machinery in Mathlib)
theorem quotient_is_sabidussi ...

-- The block-subgroup lattice isomorphism
-- (Thesis: coset.tex, Proposition 14 — order iso between
--  {H : Subgroup G | stabilizer G v ≤ H} and {B : IsBlock G | v ∈ B})
-- Mathlib already has most of this via IsBlock.orbit_stabilizer_eq
-- and IsBlock.ncard_block_mul_ncard_orbit_eq
def block_subgroup_orderIso ...
```

**Mathlib deps**: `IsBlock`, `IsBlockSystem`, Modules 1–4

**Thesis ref**: `coset.tex` §4 + `background.tex` §6

---

## Dependency Graph

```
           GraphAction.lean  (Module 1)
                |
           CosetGraph.lean   (Module 2)
                |
          Representation.lean (Module 3)
               |
          Symmetric.lean     (Module 4)
               |
          Quotient.lean      (Module 5 — stretch)
```

---

## What Makes This a Good Formalization Target

1. **Fills a real Mathlib gap**: `SimpleGraph` and `MulAction` are currently
   disconnected. This builds the bridge.

2. **The proofs are short**: Sabidussi's theorem is essentially one construction
   (orbit-stabilizer) plus checking adjacency is preserved. Lorimer's theorem
   adds the double coset / involution characterization. Neither requires heavy
   machinery beyond what Mathlib already has.

3. **The hard infrastructure exists**: Mathlib has `orbitEquivQuotientStabilizer`,
   `DoubleCoset`, `IsBlock`, `IsPretransitive`, `Quotient.lift₂`. We're
   assembling existing pieces, not building from scratch.

4. **Computational oracle**: The GAP code in `~/git/graphviz/` (especially
   `psl2_graphs.g` with its `SabidussiGraph(G, H, a)` function) has verified
   these constructions for hundreds of groups. We know exactly what the
   theorems should say.

5. **Mathlib PR potential**: Modules 1–3 are plausible Mathlib contributions.
   The `SimpleGraph.cosetGraph` definition and its vertex-transitivity would
   be the first connection between algebraic and combinatorial graph theory
   in Mathlib.

---

## Known Technical Risks

- **`Quotient.lift₂` for adjacency**: Defining `Adj` on `G ⧸ H` requires
  showing the predicate `xy⁻¹ ∈ D` is well-defined on coset representatives.
  This needs `D` to be a union of double cosets (which `HaH` is by definition).
  The proof is: if `x' = hx` and `y' = ky`, then `x'y'⁻¹ = hx(ky)⁻¹ = hxy⁻¹k⁻¹ ∈ HaH`
  iff `xy⁻¹ ∈ HaH`. Should be straightforward but fiddly with Quotient API.

- **`DecidableEq` / `Fintype` instances**: Lean's `SimpleGraph.degree` requires
  `Fintype (neighborSet v)`. For infinite groups we'd state results without
  finiteness; for the degree formula we'd need `[Fintype G]`.

- **Left vs right conventions**: The thesis uses right actions (`α^g`);
  Mathlib's `MulAction` uses left actions (`g • α`). Cosets in the thesis are
  right cosets `Hg`; Mathlib's `G ⧸ H` is left cosets `gH`.
  **Resolution**: Use Mathlib conventions throughout. The theorems are the
  same up to taking inverses. Define `Adj` as `g⁻¹h ∈ D` rather than `gh⁻¹ ∈ D`.

---

## Computational Oracle: `~/git/graphviz/`

The sibling project `~/git/graphviz/` contains Robin's working implementation
of everything we're formalizing — hundreds of computed examples across dozens
of groups. Use it to sanity-check Lean statements before attempting proofs.

### Key GAP files

| File | What it computes |
|------|-----------------|
| `psl2_graphs.g` | **`SabidussiGraph(G, H, a)`** — the canonical implementation. Vertices = right cosets of `H`, edges = `Hx ~ Hy iff xy⁻¹ ∈ HaH`. This is exactly the construction we're formalizing. |
| `symmetric-layout.g` | **`SearchQuotients`** — enumerates subgroups of `Aut(Γ)`, computes orbit quotients, finds the block-subgroup correspondence (Module 5). Also builds named graphs: Biggs-Smith = `Sab(PSL(2,17), S₄, a)`, Petersen = `PSL(2,5)/S₃`, etc. |
| `psl2_cubic_search.g` | Census search: finds all triples `(PSL(2,q), H, a)` with `|HaH|/|H| = 3` (the cubic condition). Demonstrates the valency formula from Module 2. |
| `enumerate-quotients.g` | Enumerates all quotients of a given graph via conjugacy classes of subgroups — the computational version of Module 5. |
| `bolza_graphs.g` | Sabidussi graphs from triangle group quotients — connects to the Hurwitz surface story. |

### Key documents in graphviz

| File | Relevance |
|------|-----------|
| `CLASSIFICATION.md` | The three PSL(2,q) families via Sabidussi, torus decompositions, spectral theory |
| `RESEARCH_PROGRAM.md` | Broader programme: cubic graphs as shadows of Lie groups over 𝔽_q |
| `SYMMETRIC_EMBEDDING.md` | Theory and implementation notes for the layout algorithm |
| `cubic-bi-circulant.tex` | Paper citing Sabidussi (1964), proves `Aut(CR(p)) = C_p ⋊ C_6` |

### How to use it

- **Before writing a Lean definition**: check that the GAP code computes the
  same thing. E.g., `SabidussiGraph` uses `xy⁻¹ ∈ HaH` for adjacency on
  right cosets — our Lean version on left cosets `G ⧸ H` should use `g⁻¹h ∈ D`.
- **Before stating a theorem**: verify with a concrete example. E.g., the
  Petersen graph has `|S₃| / |a⁻¹S₃a ∩ S₃| = 6/2 = 3` — does the degree
  formula in Module 2 produce this?
- **If a proof gets stuck**: compute the specific case in GAP to see whether
  the statement is even true as written.

---

## Suggested Order of Work

1. **Module 1** first — it's small and establishes the vocabulary
2. **Module 2** next — the coset graph definition is the key contribution
3. **Module 3** — the representation theorem, the payoff
4. **Module 4** — the symmetric graph characterization (uses 1–3)
5. **Module 5** — only if 1–4 go smoothly

Start each module with `sorry`-stubs for all declarations, then fill in proofs.
Use the GAP code as a sanity check: if a Lean statement doesn't match what
`SabidussiGraph` computes, the statement is wrong.
