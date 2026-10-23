/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Sabidussi

/-!
# Certification

`#print axioms` on each headline result. The CI workflow runs this file and fails
if the output mentions `sorryAx` (a `sorry` reached the theorem) or if any of the
four reports is missing (a name failed to resolve — a silent, vacuous "proof").

A clean report lists only `[propext, Classical.choice, Quot.sound]` — Lean's
foundational axioms — meaning the result is proved with no `sorry` anywhere in its
dependency tree.

The four headline results (all top-level — `SabidussiRepresentation` and `Lorimer`
are `section`s, not `namespace`s, so the names carry no prefix):
-/

-- Sabidussi's representation theorem: every vertex-transitive graph is a coset graph.
#print axioms sabidussiIso

-- Lorimer's theorem (forward): Sab(G, H, HaH) is arc-transitive for an involution a ∉ H.
#print axioms lorimer_forward

-- Lorimer's theorem (reverse): under arc-transitivity the connection set is one double coset.
#print axioms connectionSet_eq_doubleCoset

-- Lorimer's quotient theorem: quotient of Sab(G,H,D) by K ≥ H is Sab(G,K,KDK).
#print axioms quotient_cosetGraph_iso
