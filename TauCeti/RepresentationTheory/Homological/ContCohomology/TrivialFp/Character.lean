/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.Topology.Algebra.ContinuousZModDual

/-!
# The homogeneous cocycle of a character and its cup products

A continuous character `χ : G → 𝔽_p` of a topological group `G` is a homogeneous one-cocycle
`(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` with trivial `𝔽_p` coefficients, and every class of `H¹(G, 𝔽_p)` is of
this form (`TauCeti.characterClass_surjective`), for exactly one `χ`
(`TauCeti.characterClass_injective`): with trivial coefficients the homogeneous zero-cochains are
the constants, so the differential into degree one vanishes and a class in degree one is the same
as a cocycle. This gives the classes of `H¹(G, 𝔽_p)` an explicit representative on Mathlib's
homogeneous cochains, on which the cup product `H¹ × H¹ → H²` of `TauCeti.cupFp` is computed by
the Alexander–Whitney formula `(χ ⌣ ψ) g₀ g₁ g₂ = χ (g₀⁻¹ g₁) ψ (g₁⁻¹ g₂)`.

The one consequence drawn here is a **symmetry test for the vanishing of a cup product**: the
coboundary of an invariant one-cochain `w`, evaluated at `(1, a, ab)`, is
`w 1 b - w 1 (ab) + w 1 a`, which is unchanged by exchanging `a` and `b` when they commute. So if
`χ ⌣ ψ = 0` in `H²(G, 𝔽_p)` then `χ(a) ψ(b) = χ(b) ψ(a)` for all commuting `a, b ∈ G`
(`TauCeti.mul_eq_mul_of_cupFp_characterClass_eq_zero`). Contrapositively, two characters that are
not proportional on a pair of commuting elements have a nonzero cup product; this is how the cup
product of an abelian pro-`p` group such as `ℤ_p × ℤ_p` is shown to be nondegenerate.

## Main definitions

* `TauCeti.characterCochain`, `TauCeti.characterCocycle`: the homogeneous one-cocycle
  `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ`.
* `TauCeti.characterClass`: its class in `H¹(G, 𝔽_p)`, as an `𝔽_p`-linear map from the continuous
  `𝔽_p`-dual of `G`.

## Main results

* `TauCeti.characterClass_injective`, `TauCeti.characterClass_surjective`: every class of
  `H¹(G, 𝔽_p)` is the class of exactly one character.
* `TauCeti.mul_eq_mul_of_cupFp_characterClass_eq_zero`: if `χ ⌣ ψ = 0` then
  `χ(a) ψ(b) = χ(b) ψ(a)` for commuting `a` and `b`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §1.4.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TopRep

universe u

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Homogeneous cochains with trivial coefficients -/

/-- A homogeneous zero-cochain with trivial coefficients is constant. -/
theorem homogeneousCochains_trivialFp_zero_apply_eq (a : (homogeneousCochains (trivialFp p G)).X 0)
    (g₀ g₁ : G) : a.val g₀ = a.val g₁ := by
  have h := congrArg (fun F : C(G, (trivialFp p G).V) ↦ F g₀) (a.property (g₀ * g₁⁻¹))
  simpa only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply, mul_inv_rev, inv_inv,
    inv_mul_cancel_right] using h.symm

/-- A homogeneous one-cochain with trivial coefficients is determined by its values at `(1, g)`:
`a g₀ g₁ = a 1 (g₀⁻¹ g₁)`. -/
theorem homogeneousCochains_trivialFp_one_apply_eq (a : (homogeneousCochains (trivialFp p G)).X 1)
    (g₀ g₁ : G) : a.val g₀ g₁ = a.val 1 (g₀⁻¹ * g₁) := by
  have h := congrArg (fun F : C(G, C(G, (trivialFp p G).V)) ↦ F g₀ g₁) (a.property g₀)
  simpa only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply, inv_mul_cancel]
    using h.symm

/-- With trivial coefficients the differential from homogeneous zero-cochains to one-cochains is
zero, the zero-cochains being the constants. -/
theorem homogeneousCochains_trivialFp_d_zero : (homogeneousCochains (trivialFp p G)).d 0 1 = 0 := by
  ext a : 2
  apply Subtype.ext
  ext g₀ g₁
  rw [homogeneousCochains.d_zero_apply, TopModuleCat.hom_zero_apply, Submodule.coe_zero,
    ContinuousMap.zero_apply, ContinuousMap.zero_apply,
    homogeneousCochains_trivialFp_zero_apply_eq p a g₁ g₀, sub_self]

/-- **The class map is injective in degree one** with trivial coefficients: a one-cocycle with
trivial class is zero, because there are no nonzero one-coboundaries. -/
theorem π_trivialFp_one_injective : Function.Injective (π (trivialFp p G) 1) :=
  (homogeneousCochains (trivialFp p G)).homologyπ_injective_of_d_eq_zero
    (CochainComplex.prev_nat_succ 0) (homogeneousCochains_trivialFp_d_zero p)

/-! ### The cocycle of a character -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ : G → 𝔽_p`,
with trivial `𝔽_p` coefficients. -/
noncomputable def characterCochain (χ : continuousZModDual p G) :
    (homogeneousCochains (trivialFp p G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialFpEquiv p G).symm (Multiplicative.toAdd (Additive.toMul χ (q.1⁻¹ * q.2))),
      continuous_of_discreteTopology.comp (continuous_toAdd.comp
        ((Additive.toMul χ).continuous.comp (continuous_fst.inv.mul continuous_snd)))⟩,
    fun g ↦ by
      ext h k
      simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk]
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of the cochain of `χ` at `(g₀, g₁)` is `χ (g₀⁻¹ g₁)`, lifted to the coefficients. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
theorem characterCochain_apply (χ : continuousZModDual p G) (g₀ g₁ : G) :
    (characterCochain p χ).val g₀ g₁ =
      (trivialFpEquiv p G).symm (Multiplicative.toAdd (Additive.toMul χ (g₀⁻¹ * g₁))) :=
  (rfl)

/-- The cochain of a character is a cocycle. -/
theorem d_characterCochain (χ : continuousZModDual p G) :
    ((homogeneousCochains (trivialFp p G)).d 1 (1 + 1)).hom (characterCochain p χ) = 0 := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply, characterCochain_apply, characterCochain_apply,
    characterCochain_apply, ← map_sub, ← map_sub, Submodule.coe_zero, ContinuousMap.zero_apply,
    ContinuousMap.zero_apply, ContinuousMap.zero_apply, ← map_zero (trivialFpEquiv p G).symm]
  congr 1
  have h : Additive.toMul χ (g₀⁻¹ * g₂) =
      Additive.toMul χ (g₀⁻¹ * g₁) * Additive.toMul χ (g₁⁻¹ * g₂) := by
    rw [← map_mul, mul_assoc, mul_inv_cancel_left]
  rw [h, toAdd_mul]
  abel

/-- The homogeneous one-cocycle `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ : G → 𝔽_p`. -/
noncomputable def characterCocycle (χ : continuousZModDual p G) : cocycles (trivialFp p G) 1 :=
  (homogeneousCochains (trivialFp p G)).cyclesMkOfEq (characterCochain p χ) (1 + 1)
    (CochainComplex.next ℕ 1) (d_characterCochain p χ)

/-- The underlying cochain of the cocycle of `χ` is `characterCochain p χ`. -/
-- Not a `simp` lemma: `simp` rewrites the ambient object
-- `(homogeneousCochains (trivialFp p G)).X 1` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form; use it with `rw` or `simp only`.
theorem iCycles_characterCocycle (χ : continuousZModDual p G) :
    (homogeneousCochains (trivialFp p G)).iCycles 1 (characterCocycle p χ) =
      characterCochain p χ :=
  HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _

/-- The cocycle of a sum of characters is the sum of their cocycles. -/
theorem characterCocycle_add (χ ψ : continuousZModDual p G) :
    characterCocycle p (χ + ψ) = characterCocycle p χ + characterCocycle p ψ := by
  apply (homogeneousCochains (trivialFp p G)).iCycles_injective 1
  rw [map_add, iCycles_characterCocycle, iCycles_characterCocycle, iCycles_characterCocycle]
  apply Subtype.ext
  ext g₀ g₁
  rw [Submodule.coe_add, ContinuousMap.add_apply, ContinuousMap.add_apply, characterCochain_apply,
    characterCochain_apply, characterCochain_apply, ← map_add, toMul_add,
    ContinuousMonoidHom.mul_apply, toAdd_mul]

/-- **The class of a character.** The `𝔽_p`-linear map from the continuous `𝔽_p`-dual of `G` to
`H¹(G, 𝔽_p)` sending `χ` to the class of the homogeneous cocycle `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)`. It is
bijective (`TauCeti.characterClass_injective`, `TauCeti.characterClass_surjective`). It is the
homogeneous counterpart of `TauCeti.cohomFpLinearEquivContinuousZModDual`, which identifies
`H¹(G, 𝔽_p)` with the continuous dual through inhomogeneous cocycles; the two are not compared
here, and this one is the form a cup-product computation on homogeneous cochains consumes. -/
noncomputable def characterClass : continuousZModDual p G →ₗ[ZMod p] cohomFp p G 1 :=
  (AddMonoidHom.mk' (fun χ ↦ π (trivialFp p G) 1 (characterCocycle p χ)) fun χ ψ ↦ by
    rw [characterCocycle_add, map_add]).toZModLinearMap p

/-- The class of a character is the class of its homogeneous cocycle. -/
theorem characterClass_apply (χ : continuousZModDual p G) :
    characterClass p χ = π (trivialFp p G) 1 (characterCocycle p χ) :=
  (rfl)

/-- **Distinct characters have distinct classes**: `χ ↦ [χ]` is injective, because with trivial
coefficients there are no nonzero one-coboundaries. -/
theorem characterClass_injective : Function.Injective (characterClass p (G := G)) := by
  intro χ ψ h
  have hz : characterCocycle p χ = characterCocycle p ψ := π_trivialFp_one_injective p h
  have h1 := congrArg (fun z ↦ ((homogeneousCochains (trivialFp p G)).iCycles 1 z).val 1) hz
  simp only [iCycles_characterCocycle] at h1
  apply Additive.toMul.injective
  ext g
  have h2 := ContinuousMap.congr_fun h1 g
  rw [characterCochain_apply, characterCochain_apply, inv_one, one_mul] at h2
  exact Multiplicative.toAdd.injective ((trivialFpEquiv p G).symm.injective h2)

/-- **Every class of `H¹(G, 𝔽_p)` is the class of a character**: a homogeneous one-cocycle `z`
with trivial coefficients is the cocycle of the character `g ↦ z 1 g`. -/
theorem characterClass_surjective : Function.Surjective (characterClass p (G := G)) := by
  intro c
  obtain ⟨z, rfl⟩ := (homogeneousCochains (trivialFp p G)).homologyπ_surjective 1 c
  set w := (homogeneousCochains (trivialFp p G)).iCycles 1 z with hw
  have hcoc := homogeneousCochains.apply_eq_add_of_d_eq_zero
    ((homogeneousCochains (trivialFp p G)).d_iCycles_apply (1 + 1) z)
  -- The character `g ↦ w 1 g`: additivity is the cocycle identity at `(1, g, g h)` together with
  -- the invariance `w g (g h) = w 1 h`.
  let χ : G →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (trivialFpEquiv p G (w.val 1 g)))
        fun g h ↦ by
          rw [← ofAdd_add, ← map_add, hcoc 1 g (g * h),
            homogeneousCochains_trivialFp_one_apply_eq p w g (g * h), inv_mul_cancel_left]
      continuous_toFun :=
        continuous_ofAdd.comp (continuous_of_discreteTopology.comp (w.val 1).continuous) }
  refine ⟨Additive.ofMul χ, ?_⟩
  rw [characterClass_apply]
  congr 1
  apply (homogeneousCochains (trivialFp p G)).iCycles_injective 1
  rw [iCycles_characterCocycle]
  apply Subtype.ext
  ext g₀ g₁
  rw [characterCochain_apply, homogeneousCochains_trivialFp_one_apply_eq p w g₀ g₁]
  -- The value of `χ` is the lift of `w 1 (g₀⁻¹ * g₁)`, by the definition of `χ`.
  have hχ : Additive.toMul (Additive.ofMul χ) (g₀⁻¹ * g₁) =
      Multiplicative.ofAdd (trivialFpEquiv p G (w.val 1 (g₀⁻¹ * g₁))) := rfl
  rw [hχ, toAdd_ofAdd, LinearEquiv.symm_apply_apply]

/-! ### The symmetry test for the cup product -/

/-- **A vanishing cup product forces a symmetry on commuting elements.** If the cup product of the
classes of the characters `χ` and `ψ` vanishes in `H²(G, 𝔽_p)`, then `χ(a) ψ(b) = χ(b) ψ(a)` for
every pair of commuting elements `a, b` of `G`. Indeed the cup product is then the coboundary of an
invariant one-cochain `w`, whose value at `(1, a, ab)` is `w 1 b - w 1 (ab) + w 1 a`, which is
symmetric in `a` and `b` when `ab = ba`. -/
theorem mul_eq_mul_of_cupFp_characterClass_eq_zero {χ ψ : continuousZModDual p G}
    (h : cupFp p G (characterClass p χ) (characterClass p ψ) = 0) {a b : G} (hab : Commute a b) :
    Multiplicative.toAdd (Additive.toMul χ a) * Multiplicative.toAdd (Additive.toMul ψ b) =
      Multiplicative.toAdd (Additive.toMul χ b) * Multiplicative.toAdd (Additive.toMul ψ a) := by
  rw [characterClass_apply, characterClass_apply, cupFp_π] at h
  obtain ⟨w, hw⟩ := ((homogeneousCochains (trivialFp p G)).homologyπ_eq_zero_iff 2 (m := 1)
    (CochainComplex.prev_nat_succ 1)).1 h
  -- The coboundary of `w` is the cup product of the two cocycles, as homogeneous two-cochains.
  have hw' := congrArg ((homogeneousCochains (trivialFp p G)).iCycles (1 + 1)) hw
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_characterCocycle, iCycles_characterCocycle] at hw'
  -- Evaluate at `(1, a, a * b)` and at `(1, b, b * a)`.
  have h₁ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val hw') 1) a) (a * b)
  have h₂ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val hw') 1) b) (b * a)
  -- The evaluation lemmas are stated on the carriers `C(G, C(G, C(G, X.V)))` of the resolution,
  -- which are the carriers of the homogeneous cochains only after unfolding the coinduction; `rw`
  -- unfolds that much, `simp` does not.
  rw [homogeneousCochains.d_one_apply, TopPairing.cupCochain_one_one_apply, characterCochain_apply,
    characterCochain_apply] at h₁ h₂
  simp only [fpPairing_bil_apply, LinearEquiv.apply_symm_apply, inv_one, one_mul,
    inv_mul_cancel_left] at h₁ h₂
  apply (trivialFpEquiv p G).symm.injective
  rw [← h₁, ← h₂, homogeneousCochains_trivialFp_one_apply_eq p w a (a * b),
    homogeneousCochains_trivialFp_one_apply_eq p w b (b * a), inv_mul_cancel_left,
    inv_mul_cancel_left, hab.eq]
  abel

end TauCeti
