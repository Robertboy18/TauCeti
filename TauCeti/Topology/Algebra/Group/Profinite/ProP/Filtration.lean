/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints

/-!
# Successive factors of the pro-`p` filtration

The filtration in `exists_filtration_of_isProP` adjoins at each step a generator of order `p`
modulo the preceding subgroup, fixed there by `G`. This file packages the successive quotients
as additive groups equivalent to `ZMod p`, together with triviality of their induced actions.
The ambient finite `p`-primary group need not be killed by `p`.

## Main results

* `TauCeti.exists_filtration_with_trivial_factors_of_isProP`: a stable filtration of length
  `padicValNat p (Nat.card M)` with explicit additive equivalences and trivial quotient actions.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]
  {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

/-- A finite discrete `p`-primary group with a continuous pro-`p` action has a stable filtration
whose successive quotients are additively equivalent to `ZMod p` and have trivial induced
action. Only indices below the composition length contribute a factor; the chain is constant
at `⊤` thereafter. -/
theorem exists_filtration_with_trivial_factors_of_isProP (hG : IsProP p G)
    (htors : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) :
    ∃ (N : ℕ → AddSubgroup M) (hN : ∀ i, ∀ g : G, ∀ x ∈ N i, g • x ∈ N i),
      N 0 = ⊥ ∧ Monotone N ∧
      (∀ i, padicValNat p (Nat.card M) ≤ i → N i = ⊤) ∧
      (∀ i ≤ padicValNat p (Nat.card M), Nat.card (N i) = p ^ i) ∧
      ∀ i < padicValNat p (Nat.card M),
        letI := (N i).subquotientDistribMulAction (N (i + 1)) (hN i) (hN (i + 1))
        Nonempty ((N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))) ≃+ ZMod p) ∧
          ∀ (g : G) (y : N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))), g • y = y := by
  obtain ⟨N, h0, hmono, htop, hN, hcard, hgen⟩ := exists_filtration_of_isProP hG htors
  refine ⟨N, hN, h0, hmono, htop, hcard, fun i hi ↦ ?_⟩
  obtain ⟨x, hx, hxN, hpx, hgx⟩ := hgen i hi
  exact ⟨⟨subquotientEquivZModOfEqSupZmultiples hx hxN hpx⟩,
    subquotient_smul_eq_self_of_eq_sup_zmultiples (hN i) (hN (i + 1)) hx hgx⟩

end TauCeti
