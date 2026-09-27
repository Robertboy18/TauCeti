/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.RankParity
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ElementaryAbelian

/-!
# The cyclic group of order two is a Demushkin group

The cyclic group `ℤ/p` has `H¹(ℤ/p, 𝔽_p)` and `H²(ℤ/p, 𝔽_p)` both one-dimensional, the case `d = 1`
of the dimension counts for a finite elementary abelian `p`-group. Whether it is a Demushkin group
is therefore decided by the cup square of the nonzero class of `H¹(ℤ/p, 𝔽_p)`. At an odd prime the
cup square vanishes, because the cup pairing is alternating, so `ℤ/p` is not Demushkin; this is
the rank-one case of `TauCeti.IsDemushkin.demushkinRank_ne_one_of_ne_two`. At `p = 2` the cup
square is nonzero, and **`ℤ/2` is a Demushkin group of rank one**, the first example of the theory
(Labute, p. 106).

The cup square is computed on Mathlib's homogeneous cochains. The nonzero class of `H¹(ℤ/2, 𝔽₂)`
is represented by the homogeneous cocycle `(g₀, g₁) ↦ g₀⁻¹ g₁`, the homogeneous form of the
identity character `ℤ/2 → 𝔽₂`; the cup square of that cocycle is the homogeneous two-cochain
`(g₀, g₁, g₂) ↦ (g₀⁻¹ g₁) (g₁⁻¹ g₂)`, which takes the value `1` at `(1, s, 1)` and `0` at
`(1, 1, 1)`, where `s` is the generator. A homogeneous one-cochain `b` is invariant, so
`b s 1 = b 1 s`, and its coboundary takes the value `b 1 1` at both `(1, s, 1)` and `(1, 1, 1)`;
hence the cup square is not a coboundary.

## Main results

* `TauCeti.finrank_cohomFp_one_multiplicative_zmod` and
  `TauCeti.finrank_cohomFp_two_multiplicative_zmod`: `H¹(ℤ/p, 𝔽_p)` and `H²(ℤ/p, 𝔽_p)` are
  one-dimensional.
* `TauCeti.cupFp_π_cyclicTwoCocycle_self_ne_zero`: the cup square of the class of the homogeneous
  cocycle `(g₀, g₁) ↦ g₀⁻¹ g₁` in `H¹(ℤ/2, 𝔽₂)` is nonzero.
* `TauCeti.isDemushkin_multiplicative_zmod_two`: **`ℤ/2` is a Demushkin group at `p = 2`**, and
  `TauCeti.demushkinRank_multiplicative_zmod_two`: its rank is `1`.
* `TauCeti.not_isDemushkin_multiplicative_zmod_of_ne_two`: at an odd prime, `ℤ/p` is not Demushkin.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open CategoryTheory TauCeti.ContCohomology _root_.ContinuousCohomology TopRep

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the explicit `H²(G, 𝔽_p)` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

/-! ### The cohomology of `ℤ/p` in degrees one and two -/

section ZMod

variable (p : ℕ) [Fact p.Prime]

/-- **`H¹(ℤ/p, 𝔽_p)` is one-dimensional**: the cyclic group `ℤ/p` has topological generator rank
one. -/
theorem finrank_cohomFp_one_multiplicative_zmod :
    Module.finrank (ZMod p) (cohomFp p (Multiplicative (ZMod p)) 1) = 1 := by
  rw [(isProP_of_proPFrattini_eq_bot
    (proPFrattini_multiplicative_zmod_eq_bot p)).finrank_cohomFp_one
    isTopologicallyFinitelyGenerated_of_fg, topologicalGeneratorRankNat_multiplicative_zmod]

/-- **`H²(ℤ/p, 𝔽_p)` is one-dimensional**: the relation rank of the cyclic group `ℤ/p` is `1`. -/
theorem finrank_cohomFp_two_multiplicative_zmod :
    Module.finrank (ZMod p) (cohomFp p (Multiplicative (ZMod p)) 2) = 1 := by
  have hp : p.Prime := Fact.out
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed. Its
  -- scalar multiplication is installed first, as a local instance: Mathlib's `Multiplicative.smul`
  -- otherwise lets `Multiplicative (ZMod p)` act on `ZMod p` by translation, and instance
  -- resolution would pick that action.
  let : SMul (Multiplicative (ZMod p)) (ZMod p) := ⟨fun _ m ↦ m⟩
  let : DistribMulAction (Multiplicative (ZMod p)) (ZMod p) :=
    { one_smul := fun _ ↦ rfl, mul_smul := fun _ _ _ ↦ rfl, smul_zero := fun _ ↦ rfl,
      smul_add := fun _ _ _ ↦ rfl }
  have htriv : ∀ (g : Multiplicative (ZMod p)) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul (Multiplicative (ZMod p)) (ZMod p) :=
    ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  -- `H²(ℤ/p, 𝔽_p)` has `p ^ (1 · 2 / 2) = p` elements.
  have hc : Nat.card (H2 (Multiplicative (ZMod p)) (ZMod p)) = p := by
    rw [natCard_H2_of_proPFrattini_eq_bot isTopologicallyFinitelyGenerated_of_fg
      (proPFrattini_multiplicative_zmod_eq_bot p), topologicalGeneratorRankNat_multiplicative_zmod]
    norm_num
  have : Finite (H2 (Multiplicative (ZMod p)) (ZMod p)) :=
    Nat.finite_of_card_ne_zero (hc.trans_ne hp.ne_zero)
  have : Module.Finite (ZMod p) (H2 (Multiplicative (ZMod p)) (ZMod p)) := Module.Finite.of_finite
  rw [(cohomFpLinearEquivH2 p (Multiplicative (ZMod p)) htriv).finrank_eq]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := H2 (Multiplicative (ZMod p)) (ZMod p))
  rw [hc, Nat.card_zmod] at hpow
  exact Nat.pow_right_injective hp.two_le (hpow.symm.trans (pow_one p).symm)

/-- **At an odd prime, `ℤ/p` is not a Demushkin group**: it has rank one, and the rank of a
Demushkin group at an odd prime is even. -/
theorem not_isDemushkin_multiplicative_zmod_of_ne_two (hp : p ≠ 2) :
    ¬ IsDemushkin p (Multiplicative (ZMod p)) := fun h ↦
  h.demushkinRank_ne_one_of_ne_two hp
    (by rw [demushkinRank_def, topologicalGeneratorRankNat_multiplicative_zmod])

end ZMod

/-! ### The cup square of the generator of `H¹(ℤ/2, 𝔽₂)` -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ g₀⁻¹ g₁` of `ℤ/2` with trivial `𝔽₂` coefficients: the
homogeneous form of the identity character `ℤ/2 → 𝔽₂`. -/
noncomputable def cyclicTwoCochain :
    (homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ↦
      (trivialFpEquiv 2 (Multiplicative (ZMod 2))).symm (Multiplicative.toAdd (q.1⁻¹ * q.2)),
      continuous_of_discreteTopology⟩, fun g ↦ by
    ext h k
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
      ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of the cochain `cyclicTwoCochain` at `(g₀, g₁)` is `g₀⁻¹ g₁`, read in `𝔽₂`. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
theorem cyclicTwoCochain_apply (g₀ g₁ : Multiplicative (ZMod 2)) :
    cyclicTwoCochain.val g₀ g₁ =
      (trivialFpEquiv 2 (Multiplicative (ZMod 2))).symm (Multiplicative.toAdd (g₀⁻¹ * g₁)) :=
  (rfl)

/-- The cochain `cyclicTwoCochain` is a cocycle: `g₀⁻¹ g₁` is additive in the sense
`g₁⁻¹ g₂ - g₀⁻¹ g₂ + g₀⁻¹ g₁ = 0`. -/
theorem d_cyclicTwoCochain :
    ((homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).d 1 (1 + 1)).hom
      cyclicTwoCochain = 0 := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply, cyclicTwoCochain_apply, cyclicTwoCochain_apply,
    cyclicTwoCochain_apply, ← map_sub, ← map_sub]
  simp only [toAdd_mul, toAdd_inv, Submodule.coe_zero, ContinuousMap.zero_apply]
  rw [← map_zero (trivialFpEquiv 2 (Multiplicative (ZMod 2))).symm]
  congr 1
  abel

/-- The homogeneous one-cocycle `(g₀, g₁) ↦ g₀⁻¹ g₁` of `ℤ/2` with trivial `𝔽₂` coefficients. -/
noncomputable def cyclicTwoCocycle : cocycles (trivialFp 2 (Multiplicative (ZMod 2))) 1 :=
  (homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).cyclesMkOfEq cyclicTwoCochain
    (1 + 1) (CochainComplex.next ℕ 1) d_cyclicTwoCochain

/-- The underlying homogeneous cochain of `cyclicTwoCocycle` is `cyclicTwoCochain`. -/
theorem iCycles_cyclicTwoCocycle :
    (homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).iCycles 1 cyclicTwoCocycle =
      cyclicTwoCochain :=
  HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _

/-- **The cup square of the generator of `H¹(ℤ/2, 𝔽₂)` is nonzero.** The cup square of the
homogeneous cocycle `(g₀, g₁) ↦ g₀⁻¹ g₁` is the two-cochain `(g₀, g₁, g₂) ↦ (g₀⁻¹ g₁) (g₁⁻¹ g₂)`,
which is not the coboundary of any invariant one-cochain. -/
theorem cupFp_π_cyclicTwoCocycle_self_ne_zero :
    cupFp 2 (Multiplicative (ZMod 2)) (π (trivialFp 2 (Multiplicative (ZMod 2))) 1 cyclicTwoCocycle)
      (π (trivialFp 2 (Multiplicative (ZMod 2))) 1 cyclicTwoCocycle) ≠ 0 := by
  rw [cupFp_π]
  intro hzero
  obtain ⟨b, hb⟩ :=
    ((homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).homologyπ_eq_zero_iff 2 (m := 1)
      (CochainComplex.prev_nat_succ 1)).1 hzero
  have hs : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
  have hss : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
  -- The coboundary of `b` is the cup square of the cocycle, as homogeneous two-cochains.
  have h := congrArg ((homogeneousCochains (trivialFp 2 (Multiplicative (ZMod 2)))).iCycles (1 + 1))
    hb
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_cyclicTwoCocycle] at h
  -- Evaluate at `(1, s, 1)` and at `(1, 1, 1)`, where `s` is the generator.
  have h₁ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val h) 1) (Multiplicative.ofAdd 1)) 1
  have h₂ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val h) 1) 1) 1
  -- The evaluation lemmas are stated on the carriers `C(G, C(G, C(G, X.V)))` of the resolution,
  -- which are the carriers of the homogeneous cochains only after unfolding the coinduction; `rw`
  -- unfolds that much, `simp` does not.
  rw [homogeneousCochains.d_one_apply, TopPairing.cupCochain_one_one_apply] at h₁ h₂
  rw [cyclicTwoCochain_apply, cyclicTwoCochain_apply] at h₁
  rw [cyclicTwoCochain_apply] at h₂
  simp only [fpPairing_bil_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  -- The one-cochain `b` is invariant, so `b s 1 = b 1 s`.
  have hinv : b.val (Multiplicative.ofAdd 1) 1 = b.val 1 (Multiplicative.ofAdd 1) := by
    have := congrArg (fun F : C(Multiplicative (ZMod 2), C(Multiplicative (ZMod 2),
      (trivialFp 2 (Multiplicative (ZMod 2))).V)) ↦ F 1 (Multiplicative.ofAdd 1))
      (b.property (Multiplicative.ofAdd 1))
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply, hs, mul_one, hss]
      at this
    exact this
  rw [hinv] at h₁
  -- Read both equations in `𝔽₂` through the universe lift.
  have h₁' := congrArg (trivialFpEquiv 2 (Multiplicative (ZMod 2))) h₁
  have h₂' := congrArg (trivialFpEquiv 2 (Multiplicative (ZMod 2))) h₂
  simp only [map_sub, LinearEquiv.apply_symm_apply] at h₁' h₂'
  generalize trivialFpEquiv 2 (Multiplicative (ZMod 2)) (b.val 1 (Multiplicative.ofAdd 1)) = u
    at h₁'
  generalize trivialFpEquiv 2 (Multiplicative (ZMod 2)) (b.val 1 1) = v at h₁' h₂'
  revert u v
  decide

/-! ### `ℤ/2` is Demushkin -/

/-- **The cyclic group `ℤ/2` is a Demushkin group at `p = 2`**: `H¹(ℤ/2, 𝔽₂)` and `H²(ℤ/2, 𝔽₂)`
are one-dimensional, and the cup square of the generator of `H¹(ℤ/2, 𝔽₂)` is nonzero. -/
theorem isDemushkin_multiplicative_zmod_two : IsDemushkin 2 (Multiplicative (ZMod 2)) := by
  have hP : IsProP 2 (Multiplicative (ZMod 2)) :=
    isProP_of_proPFrattini_eq_bot (proPFrattini_multiplicative_zmod_eq_bot 2)
  have hfin : Module.Finite (ZMod 2) (cohomFp 2 (Multiplicative (ZMod 2)) 1) :=
    hP.finite_cohomFp_one_iff.2 isTopologicallyFinitelyGenerated_of_fg
  -- `H¹(ℤ/2, 𝔽₂)` is one-dimensional, so it has exactly one nonzero element.
  have hcard : Nat.card (cohomFp 2 (Multiplicative (ZMod 2)) 1) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_cohomFp_one_multiplicative_zmod,
      Nat.card_zmod, pow_one]
  -- The cup square of the nonzero class is nonzero, and every nonzero class is that class.
  have hx := cupFp_π_cyclicTwoCocycle_self_ne_zero
  set x := π (trivialFp 2 (Multiplicative (ZMod 2))) 1 cyclicTwoCocycle
  have hx0 : x ≠ 0 := fun h ↦ hx (by rw [h]; simp)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : cohomFp 2 (Multiplicative (ZMod 2)) 1)).1 hcard
  have key : ∀ a : cohomFp 2 (Multiplicative (ZMod 2)) 1, a ≠ 0 → a = x :=
    fun a ha ↦ (hy a ha).trans (hy x hx0).symm
  exact
    { isProP := hP
      finite_cohomFp_one := hfin
      finrank_cohomFp_two := finrank_cohomFp_two_multiplicative_zmod 2
      cup_separatingLeft := fun a ha ↦ ⟨x, by rw [key a ha]; exact hx⟩
      cup_separatingRight := fun b hb ↦ ⟨x, by rw [key b hb]; exact hx⟩ }

/-- **`ℤ/2` is a Demushkin group of rank one.** -/
@[simp]
theorem demushkinRank_multiplicative_zmod_two :
    demushkinRank isDemushkin_multiplicative_zmod_two = 1 := by
  rw [demushkinRank_def, topologicalGeneratorRankNat_multiplicative_zmod]

end TauCeti
