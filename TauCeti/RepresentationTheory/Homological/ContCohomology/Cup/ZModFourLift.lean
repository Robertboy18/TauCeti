/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp

/-!
# Cup squares of classes of `H¹(G, 𝔽₂)` that lift to `ℤ/4`

Let `G` be a topological group and `φ : G →ₜ* ℤ/4` a continuous character. Its reduction modulo
`2` is a continuous character `G → 𝔽₂`, whose class in `H¹(G, 𝔽₂)` is
`TauCeti.zmodFourReductionClass φ`, the class of the homogeneous cocycle
`(g₀, g₁) ↦ φ(g₀⁻¹ g₁) mod 2`. The cup square of this class vanishes: for `u, v ∈ ℤ/4` the carry
function `⌊·/2⌋ : ℤ/4 → 𝔽₂` satisfies `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`, so
the cup square `(g₀, g₁, g₂) ↦ (φ(g₀⁻¹ g₁) mod 2)(φ(g₁⁻¹ g₂) mod 2)` is the coboundary of the
homogeneous one-cochain `(g₀, g₁) ↦ ⌊φ(g₀⁻¹ g₁)/2⌋`. This is the vanishing half of the classical
identification of the cup square on `H¹(G, 𝔽₂)` with the Bockstein of `0 → 𝔽₂ → ℤ/4 → 𝔽₂ → 0`,
which kills exactly the classes that lift to `ℤ/4`; only the vanishing on lifted classes is proved
here. The class is nonzero as soon as `φ` takes an odd value.

Together with the nonvanishing of the cup square of the generator of `H¹(ℤ/2, 𝔽₂)`, this is what
distinguishes `ℤ/2` from the cyclic groups `ℤ/2ᵏ`, `k ≥ 2`, whose mod-`2` character lifts to
`ℤ/4`: the cup pairing on `H¹(ℤ/2ᵏ, 𝔽₂)` vanishes for `k ≥ 2`.

## Main declarations

* `TauCeti.zmodFourReductionClass`: the class in `H¹(G, 𝔽₂)` of the reduction modulo `2` of a
  continuous character `φ : G →ₜ* ℤ/4`.
* `TauCeti.zmodFourReductionClass_ne_zero`: the class is nonzero when `φ` takes an odd value.
* `TauCeti.cupFp_zmodFourReductionClass_self`: **the cup square of the class vanishes**.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TopRep

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod 2`, so that the cochain
-- computations below take place in the additive group the cohomology API expects, as in
-- `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CyclicTwo`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (φ : G →ₜ* Multiplicative (ZMod 4))

/-! ### The carry identity in `ℤ/4` -/

/-- The carry function `⌊x / 2⌋ : ℤ/4 → 𝔽₂`. -/
private def zmodFourHalf (x : ZMod 4) : ZMod 2 := ((x.val / 2 : ℕ) : ZMod 2)

/-- **The carry identity**: `⌊v/2⌋ - (⌊(u + v)/2⌋ - ⌊u/2⌋) = (u mod 2)(v mod 2)` in `𝔽₂`. This is
the coboundary equation of the cochain computation below. -/
private theorem zmodFourHalf_sub_sub (u v : ZMod 4) :
    zmodFourHalf v - (zmodFourHalf (u + v) - zmodFourHalf u) =
      ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) u *
        ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) v := by
  revert u v
  decide

/-! ### The homogeneous cochains attached to `φ` -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ f (φ (g₀⁻¹ g₁))` of `G` with trivial `𝔽₂`
coefficients, for a function `f : ℤ/4 → 𝔽₂`. -/
private noncomputable def zmodFourCochain (f : ZMod 4 → ZMod 2) :
    (homogeneousCochains (trivialFp 2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialFpEquiv 2 G).symm (f (Multiplicative.toAdd (φ (q.1⁻¹ * q.2)))), by
      have hc : Continuous fun q : G × G ↦ q.1⁻¹ * q.2 := by fun_prop
      exact (continuous_of_discreteTopology (α := Multiplicative (ZMod 4))
        (f := fun z ↦ (trivialFpEquiv 2 G).symm (f (Multiplicative.toAdd z)))).comp
          (φ.continuous.comp hc)⟩, fun g ↦ by
    ext h k
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
      ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of `zmodFourCochain φ f` at `(g₀, g₁)` is `f (φ (g₀⁻¹ g₁))`, lifted into the
coefficient object. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
private theorem zmodFourCochain_apply (f : ZMod 4 → ZMod 2) (g₀ g₁ : G) :
    (zmodFourCochain φ f).val g₀ g₁ =
      (trivialFpEquiv 2 G).symm (f (Multiplicative.toAdd (φ (g₀⁻¹ * g₁)))) :=
  (rfl)

omit [IsTopologicalGroup G] in
/-- `φ` turns products into sums of exponents. -/
private theorem toAdd_mul_of_hom (x y : G) :
    Multiplicative.toAdd (φ (x * y)) =
      Multiplicative.toAdd (φ x) + Multiplicative.toAdd (φ y) := by
  rw [map_mul, toAdd_mul]

omit [IsTopologicalGroup G] in
/-- The reduction modulo `2` of `φ` is additive. -/
private theorem castHom_toAdd_mul (x y : G) :
    ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ (x * y))) =
      ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ x)) +
        ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ y)) := by
  rw [map_mul, toAdd_mul, map_add]

/-- The cochain of the reduction modulo `2` of `φ` is a cocycle. -/
private theorem d_zmodFourCochain_castHom :
    ((homogeneousCochains (trivialFp 2 G)).d 1 (1 + 1)).hom
      (zmodFourCochain φ (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))) = 0 := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply, zmodFourCochain_apply, zmodFourCochain_apply,
    zmodFourCochain_apply, ← map_sub, ← map_sub]
  have hmul : g₀⁻¹ * g₂ = (g₀⁻¹ * g₁) * (g₁⁻¹ * g₂) := by group
  rw [hmul, castHom_toAdd_mul φ (g₀⁻¹ * g₁) (g₁⁻¹ * g₂)]
  simp only [Submodule.coe_zero, ContinuousMap.zero_apply]
  rw [← map_zero (trivialFpEquiv 2 G).symm]
  congr 1
  abel

/-- The homogeneous one-cocycle `(g₀, g₁) ↦ φ (g₀⁻¹ g₁) mod 2`. -/
private noncomputable def zmodFourCocycle : cocycles (trivialFp 2 G) 1 :=
  (homogeneousCochains (trivialFp 2 G)).cyclesMkOfEq
    (zmodFourCochain φ (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)))
    (1 + 1) (CochainComplex.next ℕ 1) (d_zmodFourCochain_castHom φ)

/-- The underlying homogeneous cochain of `zmodFourCocycle φ`. -/
private theorem iCycles_zmodFourCocycle :
    (homogeneousCochains (trivialFp 2 G)).iCycles 1 (zmodFourCocycle φ) =
      zmodFourCochain φ (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) :=
  HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _

/-! ### The class and its cup square -/

/-- **The class in `H¹(G, 𝔽₂)` of the reduction modulo `2` of a continuous character
`φ : G →ₜ* ℤ/4`**: the class of the homogeneous cocycle `(g₀, g₁) ↦ φ (g₀⁻¹ g₁) mod 2`. -/
noncomputable def zmodFourReductionClass : cohomFp 2 G 1 :=
  π (trivialFp 2 G) 1 (zmodFourCocycle φ)

/-- **The class of the reduction of `φ` is nonzero when `φ` takes an odd value**: a homogeneous
zero-cochain is a constant function, so its coboundary vanishes, while the cocycle takes the
value `φ g mod 2 ≠ 0` at `(1, g)`. -/
theorem zmodFourReductionClass_ne_zero {g : G}
    (hg : ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ g)) ≠ 0) :
    zmodFourReductionClass φ ≠ 0 := by
  intro hzero
  obtain ⟨b, hb⟩ :=
    ((homogeneousCochains (trivialFp 2 G)).homologyπ_eq_zero_iff 1 (m := 0)
      (CochainComplex.prev_nat_succ 0)).1 hzero
  -- The coboundary of `b` is the cocycle, as homogeneous one-cochains.
  have h := congrArg ((homogeneousCochains (trivialFp 2 G)).iCycles (0 + 1)) hb
  rw [HomologicalComplex.iCycles_toCycles_apply, iCycles_zmodFourCocycle] at h
  -- Evaluate at `(1, g)`.
  have h₁ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (congrArg Subtype.val h) 1) g
  -- The evaluation lemmas are stated on the carriers of the resolution, which are the carriers
  -- of the homogeneous cochains only after unfolding the coinduction; `rw` unfolds that much,
  -- `simp` does not.
  rw [homogeneousCochains.d_zero_apply, zmodFourCochain_apply, inv_one, one_mul] at h₁
  -- The zero-cochain `b` is invariant, hence constant: `b g = b 1`.
  have hinv : b.val g = b.val 1 := by
    have := congrArg (fun F : C(G, (trivialFp 2 G).V) ↦ F g) (b.property g)
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
      inv_mul_cancel] at this
    exact this.symm
  rw [hinv, sub_self] at h₁
  exact hg (by simpa using (congrArg (trivialFpEquiv 2 G) h₁).symm)

/-- **The cup square of a class of `H¹(G, 𝔽₂)` that lifts to `ℤ/4` vanishes.** The cup square of
the cocycle `(g₀, g₁) ↦ φ (g₀⁻¹ g₁) mod 2` is the coboundary of the homogeneous one-cochain
`(g₀, g₁) ↦ ⌊φ (g₀⁻¹ g₁) / 2⌋`, by the carry identity in `ℤ/4`. -/
@[simp]
theorem cupFp_zmodFourReductionClass_self :
    cupFp 2 G (zmodFourReductionClass φ) (zmodFourReductionClass φ) = 0 := by
  rw [zmodFourReductionClass, cupFp_π,
    (homogeneousCochains (trivialFp 2 G)).homologyπ_eq_zero_iff 2 (m := 1)
      (CochainComplex.prev_nat_succ 1)]
  refine ⟨zmodFourCochain φ zmodFourHalf, ?_⟩
  apply (homogeneousCochains (trivialFp 2 G)).iCycles_injective (n := 1 + 1)
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_zmodFourCocycle]
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply]
  rw [TopPairing.cupCochain_one_one_apply]
  rw [zmodFourCochain_apply, zmodFourCochain_apply, zmodFourCochain_apply]
  rw [zmodFourCochain_apply, zmodFourCochain_apply]
  rw [fpPairing_bil_apply]
  simp only [LinearEquiv.apply_symm_apply]
  rw [← map_sub (trivialFpEquiv 2 G).symm, ← map_sub (trivialFpEquiv 2 G).symm]
  have hmul : g₀⁻¹ * g₂ = (g₀⁻¹ * g₁) * (g₁⁻¹ * g₂) := by group
  refine congrArg (trivialFpEquiv 2 G).symm ?_
  rw [hmul, toAdd_mul_of_hom φ (g₀⁻¹ * g₁) (g₁⁻¹ * g₂)]
  exact zmodFourHalf_sub_sub _ _

end TauCeti
