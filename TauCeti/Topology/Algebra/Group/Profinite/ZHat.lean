/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Completion
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Commutative

/-!
# The profinite integers as a profinite group

The **profinite integers** `ℤ̂`, written `zHat`, form the profinite completion of the additive
group of `ℤ`, written multiplicatively. This file records the group-theoretic facts about `ℤ̂`
that the pro-`p` theory uses; the ring structure on `ℤ̂` is not treated here.

The generator `1 ∈ ℤ` gives the topological generator `zHat.gen`, and the universal property of
the profinite completion becomes: continuous homomorphisms from `ℤ̂` to a profinite group `P`
are exactly the elements of `P`, through the value at `zHat.gen`. Since the image of `ℤ` is
dense, `ℤ̂` is commutative.

The main result identifies the maximal pro-`p` quotient of `ℤ̂` with the additive group of the
`p`-adic integers, `maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p]`: both represent the
same functor on pro-`p` groups, a continuous homomorphism out of either being an element of the
target, and the isomorphism carries the class of `zHat.gen` to `1`. No product decomposition of
`ℤ̂` over the primes is used. Combined with the fact that a Sylow pro-`p` subgroup of a
commutative profinite group maps isomorphically onto the maximal pro-`p` quotient, every
`p`-Sylow subgroup of `ℤ̂` is topologically isomorphic to `ℤ_p`.

## Main definitions

* `TauCeti.zHat`: the profinite integers, as a profinite group.
* `TauCeti.zHat.ofInt`, `TauCeti.zHat.gen`: the canonical homomorphism from `ℤ` and the image
  of `1`.
* `TauCeti.zHat.lift`: the continuous homomorphism to a profinite group sending `zHat.gen` to a
  given element.
* `TauCeti.zHat.maximalProPQuotientEquivPadicInt`: the maximal pro-`p` quotient of `ℤ̂` is the
  additive group of `ℤ_[p]`.
* `TauCeti.IsProPSylow.continuousMulEquivPadicInt`: every `p`-Sylow subgroup of `ℤ̂` is the
  additive group of `ℤ_[p]`.

## Main results

* `TauCeti.zHat.hom_ext`, `TauCeti.zHat.existsUnique_lift`: the universal property of `ℤ̂`.
* `TauCeti.zHat.denseRange_ofInt`, and the `IsMulCommutative zHat` instance: the image of `ℤ`
  is dense, so `ℤ̂` is commutative.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.3.
-/

public section

namespace TauCeti

open CategoryTheory

universe v

/-- The **profinite integers** `ℤ̂`: the profinite completion of the additive group of `ℤ`,
written multiplicatively. This is the profinite group only; its ring structure is not treated
here. -/
noncomputable abbrev zHat : ProfiniteGrp.{0} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

namespace zHat

/-- The canonical homomorphism from `ℤ`, written multiplicatively, to the profinite integers. It
is Mathlib's unit `ProfiniteGrp.ProfiniteCompletion.eta` at `Multiplicative ℤ`, read as a plain
monoid homomorphism. -/
noncomputable def ofInt : Multiplicative ℤ →* zHat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

/-- The underlying function of `ofInt` is the unit map into the profinite completion. -/
theorem coe_ofInt :
    ⇑ofInt = ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ)) :=
  (rfl)

/-- The image of `1 ∈ ℤ` in the profinite integers: the element whose value determines a
continuous homomorphism out of `ℤ̂`, by `zHat.hom_ext`. -/
noncomputable def gen : zHat := ofInt (Multiplicative.ofAdd 1)

/-- The canonical homomorphism from `ℤ` sends `n` to the `n`-th power of the generator. -/
@[simp]
theorem ofInt_ofAdd (n : ℤ) : ofInt (Multiplicative.ofAdd n) = gen ^ n := by
  rw [gen, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]

/-- The image of `ℤ` is dense in the profinite integers. -/
theorem denseRange_ofInt : DenseRange ofInt := by
  rw [coe_ofInt]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- The profinite integers are commutative, since the image of `ℤ` is dense. -/
instance : IsMulCommutative zHat where
  is_comm := ⟨fun x y ↦ by
    -- Multiplication by a fixed element is continuous, so it suffices to check commutation
    -- on the dense image of `ℤ`, in each variable separately.
    have h : ∀ (z : Multiplicative ℤ) (x : zHat), x * ofInt z = ofInt z * x := fun z ↦
      congrFun (denseRange_ofInt.equalizer (continuous_id.mul continuous_const)
        (continuous_const.mul continuous_id)
        (funext fun w ↦ by simp only [Function.comp, ← map_mul, mul_comm]))
    exact congrFun (denseRange_ofInt.equalizer (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const) (funext fun z ↦ h z x)) y⟩

section HomExt

variable {Q : Type v} [Monoid Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of the profinite integers into a Hausdorff topological
monoid that agree on the generator are equal. -/
@[ext]
theorem hom_ext {φ ψ : zHat →ₜ* Q} (h : φ gen = ψ gen) : φ = ψ := by
  refine ProfiniteCompletion.continuousMonoidHom_ext (Multiplicative ℤ) fun z ↦ ?_
  have hcomp : φ.toMonoidHom.comp ofInt = ψ.toMonoidHom.comp ofInt := MonoidHom.ext_mint h
  simpa [coe_ofInt] using DFunLike.congr_fun hcomp z

end HomExt

section Lift

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from the profinite integers to a profinite group `P` sending the
generator to `a`. -/
noncomputable def lift (a : P) : zHat →ₜ* P :=
  (ProfiniteCompletion.continuousMonoidHomEquiv (Multiplicative ℤ) P).symm (zpowersHom P a)

/-- The lift of `a` sends the image of `n ∈ ℤ` to `a ^ n`. -/
@[simp]
theorem lift_ofInt (a : P) (z : Multiplicative ℤ) : lift a (ofInt z) = a ^ z.toAdd := by
  rw [lift, coe_ofInt, ProfiniteCompletion.continuousMonoidHomEquiv_symm_apply_etaFn,
    zpowersHom_apply]

/-- The lift of `a` sends the generator to `a`. -/
@[simp]
theorem lift_gen (a : P) : lift a gen = a := by
  rw [gen, lift_ofInt, toAdd_ofAdd, zpow_one]

/-- A continuous homomorphism sending the generator to `a` is the lift of `a`. -/
theorem lift_unique (a : P) (φ : zHat →ₜ* P) (hφ : φ gen = a) : φ = lift a :=
  hom_ext (by rw [hφ, lift_gen])

/-- **The universal property of the profinite integers.** For every element `a` of a profinite
group there is a unique continuous homomorphism from `ℤ̂` sending the generator to `a`. -/
theorem existsUnique_lift (a : P) : ∃! φ : zHat →ₜ* P, φ gen = a :=
  ⟨lift a, lift_gen a, fun φ hφ ↦ lift_unique a φ hφ⟩

end Lift

section MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime]

/-- **The maximal pro-`p` quotient of `ℤ̂` is `ℤ_p`.** The isomorphism
`maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p]` is induced by the inclusion `ℤ → ℤ_[p]`
and carries the class of the generator to `1`; its inverse is the `p`-adic power of that class.
Both groups represent the same functor on pro-`p` groups, a continuous homomorphism out of
either being an element of the target, which is what forces the two to agree. -/
noncomputable def maximalProPQuotientEquivPadicInt :
    maximalProPQuotient p zHat ≃ₜ* Multiplicative ℤ_[p] :=
  have hZ : IsProP p (maximalProPQuotient p zHat) := isProP_maximalProPQuotient
  have hP : IsProP p (Multiplicative ℤ_[p]) := isProP_multiplicative_padicInt p
  let φ : maximalProPQuotient p zHat →* Multiplicative ℤ_[p] :=
    maximalProPQuotient.lift hP (lift (Multiplicative.ofAdd 1)).toMonoidHom
      (lift (Multiplicative.ofAdd 1)).continuous
  have hφ : Continuous φ := maximalProPQuotient.continuous_lift _ _ _
  let ψ : Multiplicative ℤ_[p] → maximalProPQuotient p zHat := fun l ↦
    hZ.padicPow (maximalProPQuotient.mk p zHat gen) l.toAdd
  have hψ : Continuous ψ :=
    hZ.continuous_padicPow.comp (continuous_toAdd.prodMk continuous_const)
  { toFun := φ
    invFun := ψ
    map_mul' := map_mul φ
    left_inv := by
      -- `ψ ∘ φ` is continuous and agrees with the identity on the dense image of `ℤ`.
      have hdense :
          DenseRange fun z : Multiplicative ℤ ↦ maximalProPQuotient.mk p zHat (ofInt z) :=
        (maximalProPQuotient.mk_surjective p zHat).denseRange.comp denseRange_ofInt
          (maximalProPQuotient.continuous_mk p zHat)
      refine congrFun (hdense.equalizer (hψ.comp hφ) continuous_id
        (funext (Multiplicative.ofAdd.surjective.forall.mpr fun n ↦ ?_)))
      simp [φ, ψ, map_zpow, toAdd_zpow, hZ.padicPow_intCast]
    right_inv l := by
      -- `φ` preserves `p`-adic powers, and the `p`-adic power of `1 ∈ ℤ_[p]` is the identity.
      simp only [ψ]
      rw [hZ.map_padicPow hP φ hφ]
      simp [φ]
    continuous_toFun := hφ
    continuous_invFun := hψ }

/-- The isomorphism from the maximal pro-`p` quotient of `ℤ̂` to `ℤ_p` is the factorisation of
the lift of `1 ∈ ℤ_[p]` through the quotient map. -/
@[simp]
theorem maximalProPQuotientEquivPadicInt_mk (x : zHat) :
    maximalProPQuotientEquivPadicInt p (x : maximalProPQuotient p zHat) =
      lift (Multiplicative.ofAdd (1 : ℤ_[p])) x :=
  maximalProPQuotient.lift_mk _ _ _ x

/-- The isomorphism from the maximal pro-`p` quotient of `ℤ̂` to `ℤ_p` sends the class of the
generator to `1`. -/
theorem maximalProPQuotientEquivPadicInt_mk_gen :
    maximalProPQuotientEquivPadicInt p (gen : maximalProPQuotient p zHat) =
      Multiplicative.ofAdd 1 := by
  simp

/-- The inverse isomorphism from `ℤ_p` to the maximal pro-`p` quotient of `ℤ̂` is the `p`-adic
power of the class of the generator. -/
@[simp]
theorem maximalProPQuotientEquivPadicInt_symm_apply (l : Multiplicative ℤ_[p]) :
    (maximalProPQuotientEquivPadicInt p).symm l =
      (isProP_maximalProPQuotient (p := p) (G := zHat)).padicPow
        (gen : maximalProPQuotient p zHat) l.toAdd :=
  -- The inverse is the `p`-adic power by definition; isolate that reduction in this opaque
  -- theorem so that the definition stays unexposed.
  (rfl)

end MaximalProPQuotient

end zHat

/-- **Every `p`-Sylow subgroup of `ℤ̂` is `ℤ_p`**: the quotient map to the maximal pro-`p`
quotient restricts to a topological group isomorphism from the Sylow subgroup, and that quotient
is the additive group of `ℤ_[p]`. -/
noncomputable def IsProPSylow.continuousMulEquivPadicInt {p : ℕ} [Fact p.Prime]
    {P : Subgroup zHat} (hP : IsProPSylow p P) : P ≃ₜ* Multiplicative ℤ_[p] :=
  hP.continuousMulEquivMaximalProPQuotient.trans (zHat.maximalProPQuotientEquivPadicInt p)

/-- The isomorphism from a `p`-Sylow subgroup of `ℤ̂` to `ℤ_p` is the composite of the quotient
map to the maximal pro-`p` quotient with its identification with `ℤ_p`. -/
theorem IsProPSylow.continuousMulEquivPadicInt_apply {p : ℕ} [Fact p.Prime]
    {P : Subgroup zHat} (hP : IsProPSylow p P) (x : P) :
    hP.continuousMulEquivPadicInt x =
      zHat.maximalProPQuotientEquivPadicInt p (maximalProPQuotient.mk p zHat x) := by
  rw [continuousMulEquivPadicInt, ContinuousMulEquiv.trans_apply,
    continuousMulEquivMaximalProPQuotient_apply]

end TauCeti
