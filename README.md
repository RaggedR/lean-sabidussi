# Sabidussi's Representation Theorem in Lean 4

[![Lean CI](https://github.com/RaggedR/lean-sabidussi/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/RaggedR/lean-sabidussi/actions/workflows/lean_action_ci.yml)

A formalization of **Sabidussi's representation theorem** for vertex-transitive
graphs and **Lorimer's theorem** on arc-transitive (symmetric) graphs, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

**736 lines of Lean 4. Zero sorry's — machine-checked.** The badge above is green
only when CI builds the whole development *and* `#print axioms` confirms that none
of the four headline theorems — `sabidussiIso` (the representation theorem),
`lorimer_forward` and `connectionSet_eq_doubleCoset` (Lorimer, both directions),
and `quotient_cosetGraph_iso` (the quotient theorem) — depends on `sorryAx`. Each
reduces to only Lean's foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`), so "zero sorry" is a verified fact rather than a claim taken on trust.

## What's here

### Core theory

| File | Content |
|------|---------|
| `GraphAction.lean` | Group actions on simple graphs. `GraphAction`, `IsVertexTransitive`, `IsArcTransitive`. Vertex-transitive + locally transitive implies arc-transitive. |
| `CosetGraph.lean` | The **coset graph** `Sab(G, H, D)`: vertices are left cosets `G/H`, edges connect `xH` to `yH` when `x⁻¹y ∈ D`. Connection set axioms (double-coset stable, symmetric, disjoint from H). Coset graphs are vertex-transitive. |
| `Representation.lean` | **Sabidussi's representation theorem**: every vertex-transitive graph is isomorphic to a coset graph. The orbit-stabilizer equivalence `V ≃ G/G_v` is a graph isomorphism to `Sab(G, G_v, D)`. |
| `Symmetric.lean` | **Lorimer's theorem** (forward): `Sab(G, H, HaH)` is arc-transitive when `a` is an involution not in `H`. (Reverse): arc-transitive graphs have a single double coset as connection set. |
| `Quotient.lean` | **Lorimer's quotient theorem**: the quotient of `Sab(G, H, D)` by a G-invariant partition is `Sab(G, K, KDK)` for an overgroup `H ≤ K ≤ G`. |

### Reference material

The `reference/` directory contains the LaTeX source of the author's honours
thesis on symmetric graphs, which provides the mathematical background for this
formalization.

## The mathematics

**Sabidussi's theorem** (1964) characterizes vertex-transitive graphs: a graph
is vertex-transitive if and only if it is isomorphic to a coset graph. The
construction takes a group `G` acting transitively on vertices, picks a
basepoint `v`, and builds the connection set `D = {g ∈ G : v ~ g·v}`. The
orbit-stabilizer bijection `V ≃ G/G_v` then becomes a graph isomorphism.

**Lorimer's theorem** refines this for *symmetric* (arc-transitive) graphs:
the connection set must be a single double coset `HaH` where `a` is an
involution. Conversely, any such double coset produces an arc-transitive graph.

The **quotient theorem** shows that quotienting `Sab(G, H, D)` by a block
system (equivalently, an overgroup `K ≥ H`) yields `Sab(G, K, KDK)` — the
quotient of a symmetric graph is again symmetric.

## References

- Langer, R., *Symmetric Graphs and their Quotients*, [arXiv:1306.4798](https://arxiv.org/abs/1306.4798)
- Sabidussi, G., *Vertex-transitive graphs*, Monatsh. Math. 68 (1964), 426-438
- Lorimer, P., *Vertex-transitive graphs: symmetric graphs of prime valency*, J. Graph Theory 8 (1984)

## Building

Requires Lean 4.30 and Mathlib.

```bash
lake build
```

## License

MIT
