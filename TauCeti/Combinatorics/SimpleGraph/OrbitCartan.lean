/-
Copyright (c) 2026 Robert Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.GroupTheory.GroupAction.Basic
public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction

import Mathlib.Tactic.Linarith

/-!
# Cartan column sums on orbits in a forest

An orbit of graph automorphisms induces a regular forest, whose degree is at most one.
Consequently the columns of the graph Cartan matrix have a common sum of one or two
when restricted to that orbit. The acting group need not be finite, and the forest need
not be connected.

For an action on simple roots, the corresponding Cartan sum follows once the root
Cartan matrix is identified with the graph Cartan matrix and the action is shown to
preserve adjacency.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nonempty finite regular forest has degree at most one. -/
theorem IsAcyclic.degree_le_one_of_isRegularOfDegree [Fintype V] [Nonempty V] {d : ℕ}
    (hG : G.IsAcyclic) (hd : G.IsRegularOfDegree d) : d ≤ 1 := by
  classical
  have he := hG.ncard_edgeSet_add_one_le_card
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [hd.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset] at he
  rw [Fintype.card_eq_nat_card] at hs
  have hv : 0 < Nat.card V := Nat.card_pos
  nlinarith

private theorem degree_eq_of_pretransitive [Fintype V]
    {Γ : Type*} [Group Γ] [MulAction Γ V]
    [MulAction.IsPretransitive Γ V]
    (hact : ∀ (g : Γ) ⦃i j : V⦄, G.Adj i j → G.Adj (g • i) (g • j))
    (i j : V) : G.degree i = G.degree j := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ i j
  let e : G ≃g G :=
    { MulAction.toPerm g with
      map_rel_iff' := by
        intro x y
        constructor
        · intro h
          simpa using hact g⁻¹ h
        · intro h
          exact hact g h }
  exact (e.degree_eq i).symm

/-- On any orbit in a finite forest, the graph Cartan matrix has a common column sum
of one or two. The sum is taken over the given finset of ambient vertices. -/
theorem IsAcyclic.exists_graphCartanMatrix_sum_orbit [Finite V] [DecidableEq V]
    {Γ : Type*} [Group Γ] [MulAction Γ V] (hG : G.IsAcyclic)
    (hact : ∀ (g : Γ) ⦃i j : V⦄, G.Adj i j → G.Adj (g • i) (g • j))
    (a : V) (s : Finset V) (hs : (s : Set V) = MulAction.orbit Γ a) :
    ∃ d : ℤ, (d = 1 ∨ d = 2) ∧
      ∀ i ∈ s, ∑ j ∈ s, G.graphCartanMatrix ℤ j i = d := by
  classical
  let := Fintype.ofFinite V
  let H := G.induce (MulAction.orbit Γ a)
  let a' : MulAction.orbit Γ a := ⟨a, MulAction.mem_orbit_self a⟩
  let : Nonempty (MulAction.orbit Γ a) := ⟨a'⟩
  have hH : H.IsAcyclic := hG.induce _
  have hreg : H.IsRegularOfDegree (H.degree a') := by
    intro i
    exact degree_eq_of_pretransitive (G := H) (Γ := Γ)
      (fun g _ _ h ↦ hact g h) i a'
  have hdegree := hH.degree_le_one_of_isRegularOfDegree hreg
  refine ⟨2 - (H.degree a' : ℤ), ?_, ?_⟩
  · have : H.degree a' = 0 ∨ H.degree a' = 1 := by omega
    rcases this with h | h <;> simp [h]
  · intro i hi
    let i' : MulAction.orbit Γ a := ⟨i, hs ▸ hi⟩
    have hrow := H.graphCartanMatrix_mulVec_apply (fun _ ↦ (1 : ℤ)) i'
    simp only [Matrix.mulVec, dotProduct, mul_one, Finset.sum_const,
      nsmul_eq_mul, H.card_neighborFinset_eq_degree, hreg.degree_eq] at hrow
    calc
      ∑ j ∈ s, G.graphCartanMatrix ℤ j i =
          ∑ j : MulAction.orbit Γ a, G.graphCartanMatrix ℤ j i := by
        exact Finset.sum_subtype s (fun x ↦ by rw [← hs]; rfl) _
      _ = ∑ j : MulAction.orbit Γ a, H.graphCartanMatrix ℤ i' j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [graphCartanMatrix_apply, H, i', Subtype.ext_iff, eq_comm, G.adj_comm]
      _ = 2 - (H.degree a' : ℤ) := hrow

end SimpleGraph
