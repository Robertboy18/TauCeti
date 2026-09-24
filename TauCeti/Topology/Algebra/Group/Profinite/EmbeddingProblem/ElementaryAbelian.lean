/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Basic

/-!
# Solvability with elementary abelian kernel

`TauCeti.HasElementaryAbelianSolutions p G` says that every finite embedding problem for `G`
with commutative kernel killed by `p` has a solution. The finite groups are taken in the universe
of `G`, as every finite group is isomorphic to one in that universe.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Solvability with elementary abelian kernel.** Every finite embedding problem for `G`, with
groups in the universe of `G`, whose kernel `ker α` is elementary abelian, that is killed by `p` and
commutative, has a solution. -/
def HasElementaryAbelianSolutions : Prop :=
  ∀ P : FiniteEmbeddingProblem.{u, u, u} G, (∀ x ∈ P.α.ker, x ^ p = 1) →
    (∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, x * y = y * x) → ∃ β : G →* P.E, P.IsSolution β

variable {p G}

/-- The defining property of `HasElementaryAbelianSolutions`, as a lemma usable outside this
module. -/
theorem hasElementaryAbelianSolutions_iff :
    HasElementaryAbelianSolutions p G ↔
      ∀ P : FiniteEmbeddingProblem.{u, u, u} G, (∀ x ∈ P.α.ker, x ^ p = 1) →
        (∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, x * y = y * x) → ∃ β : G →* P.E, P.IsSolution β :=
  Iff.rfl

end TauCeti
