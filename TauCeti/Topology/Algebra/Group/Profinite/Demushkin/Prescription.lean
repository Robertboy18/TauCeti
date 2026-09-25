/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cocycle

/-!
# Twisted coefficients `I(χ)/pⁱ` and the prescription property of a character

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character. For each `i`, the
finite discrete module `I(χ)/pⁱ` is `ℤ/pⁱ` with `G` acting by `g • x = χ(g) x`, the action being
through the truncation `charScalar χ i g` of `χ g` modulo `pⁱ`. The reductions
`I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i` are equivariant, so they induce maps on continuous cohomology.

A character has the **prescription property** when every reduction
`H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective: every continuous crossed homomorphism to
`I(χ)/p` lifts, modulo principal ones, to a continuous crossed homomorphism to `I(χ)/pⁱ`. This is
Labute's condition on the orientation of a Demushkin group: such a group has exactly one continuous
character with the prescription property, its canonical character (Labute, Thm 4). Here the
property is defined, against the explicit model of continuous cohomology, and proved for every
continuous character of a free pro-`p` group: on `F = freeProP p X` a continuous `1`-cocycle is
determined by its values on the generators and takes any prescribed values there, so lifting a
cocycle is lifting finitely many residues.

The coefficient module is placed in the universe of `G`, as a structure wrapping `ZMod (p ^ i)`,
because the universal property of a free pro-`p` group lifts maps into groups of the universe of
its generators. `I(χ)/p` is `ZModTwist χ 1`, the module at `i = 1`, with carrier `ZMod (p ^ 1)`.

## Main definitions

* `TauCeti.charScalar`: the scalar `χ g mod pⁱ` by which `g` acts, as a monoid homomorphism
  `G →* ZMod (p ^ i)`.
* `TauCeti.ZModTwist`: the twisted module `I(χ)/pⁱ`, a finite discrete `G`-module with continuous
  action.
* `TauCeti.ZModTwist.reduce`: the equivariant reduction `I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i`.
* `TauCeti.HasPrescriptionProperty`: surjectivity of every `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`.

## Main results

* `TauCeti.ZModTwist.isProP_multiplicative`: `I(χ)/pⁱ` is a finite `p`-group.
* `TauCeti.freeProP.hasPrescriptionProperty`: every continuous character of a free pro-`p` group
  has the prescription property.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2
  and Theorem 4.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The scalar of the action -/

/-- The scalar by which `g` acts on `I(χ)/pⁱ`: the truncation of `χ g` modulo `pⁱ`, as a monoid
homomorphism into the multiplicative monoid of `ZMod (p ^ i)`. -/
noncomputable def charScalar (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) : G →* ZMod (p ^ i) :=
  ((PadicInt.toZModPow i : ℤ_[p] →+* ZMod (p ^ i)) : ℤ_[p] →* ZMod (p ^ i)).comp
    ((Units.coeHom ℤ_[p]).comp χ.toMonoidHom)

variable (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)

theorem charScalar_apply (g : G) : charScalar χ i g = PadicInt.toZModPow i (χ g : ℤ_[p]) :=
  (rfl)

theorem continuous_charScalar : Continuous (charScalar χ i) :=
  (PadicInt.continuous_toZModPow i).comp (Units.continuous_val.comp χ.continuous)

/-- The scalar of the action is a unit, being the reduction of a `p`-adic unit. -/
theorem isUnit_charScalar (g : G) : IsUnit (charScalar χ i g) :=
  (χ g).isUnit.map (PadicInt.toZModPow i)

variable {i}

/-- The scalars at different levels are compatible under reduction. -/
theorem castHom_charScalar {j : ℕ} (h : j ≤ i) (g : G) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) (charScalar χ i g) = charScalar χ j g :=
  RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow j i h) _

variable (i)

/-! ### The twisted module -/

/-- **The twisted module `I(χ)/pⁱ`**: the additive group `ZMod (p ^ i)`, placed in the universe of
`G`, on which `g` acts by multiplication by the scalar `charScalar χ i g`. The character is a
parameter of the type so that the action can be an instance. -/
@[ext]
structure ZModTwist (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) : Type u where
  /-- The underlying residue class modulo `pⁱ`. -/
  val : ZMod (p ^ i)

namespace ZModTwist

/-- The identification of `I(χ)/pⁱ` with `ZMod (p ^ i)` as a type, forgetting the action. -/
def equiv : ZModTwist χ i ≃ ZMod (p ^ i) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equiv_apply (x : ZModTwist χ i) : equiv χ i x = x.val := (rfl)

@[simp] theorem equiv_symm_apply (x : ZMod (p ^ i)) : (equiv χ i).symm x = ⟨x⟩ := (rfl)

instance : AddCommGroup (ZModTwist χ i) := (equiv χ i).addCommGroup

@[simp] theorem val_zero : (0 : ZModTwist χ i).val = 0 := (rfl)

@[simp] theorem val_add (x y : ZModTwist χ i) : (x + y).val = x.val + y.val := (rfl)

@[simp] theorem val_neg (x : ZModTwist χ i) : (-x).val = -x.val := (rfl)

@[simp] theorem val_sub (x y : ZModTwist χ i) : (x - y).val = x.val - y.val := (rfl)

instance : TopologicalSpace (ZModTwist χ i) := ⊥

instance : DiscreteTopology (ZModTwist χ i) := ⟨rfl⟩

instance : Finite (ZModTwist χ i) := Finite.of_equiv _ (equiv χ i).symm

/-- `G` acts on `I(χ)/pⁱ` through the scalar `charScalar χ i`. -/
noncomputable instance : SMul G (ZModTwist χ i) where
  smul g x := ⟨charScalar χ i g * x.val⟩

@[simp]
theorem val_smul (g : G) (x : ZModTwist χ i) : (g • x).val = charScalar χ i g * x.val :=
  (rfl)

/-- The action of `G` on `I(χ)/pⁱ` through the scalar `charScalar χ i` is distributive. -/
noncomputable instance : DistribMulAction G (ZModTwist χ i) where
  one_smul x := ZModTwist.ext (by simp)
  mul_smul g h x := ZModTwist.ext (by simp [mul_assoc])
  smul_zero g := ZModTwist.ext (by simp)
  smul_add g x y := ZModTwist.ext (by simp [mul_add])

/-- The action of `G` on the discrete module `I(χ)/pⁱ` is continuous, because the scalar
`charScalar χ i` is. -/
instance : ContinuousSMul G (ZModTwist χ i) where
  continuous_smul :=
    (continuous_of_discreteTopology (f := fun q : ZMod (p ^ i) × ZModTwist χ i ↦
      (⟨q.1 * q.2.val⟩ : ZModTwist χ i))).comp
      (((continuous_charScalar χ i).comp continuous_fst).prodMk continuous_snd)

/-- `I(χ)/pⁱ` is a finite `p`-group of order `pⁱ`. -/
theorem isPGroup_multiplicative : IsPGroup p (Multiplicative (ZModTwist χ i)) :=
  IsPGroup.of_card (n := i) (by
    rw [Nat.card_congr (Multiplicative.toAdd.trans (equiv χ i)), Nat.card_zmod])

/-- `I(χ)/pⁱ`, with its discrete topology, is pro-`p`. -/
theorem isProP_multiplicative : IsProP p (Multiplicative (ZModTwist χ i)) :=
  (isPGroup_multiplicative χ i).isProP

variable {i}

/-- **The reduction `I(χ)/pⁱ → I(χ)/pʲ`** for `j ≤ i`, an equivariant additive homomorphism. -/
def reduce {j : ℕ} (h : j ≤ i) : ZModTwist χ i →+[G] ZModTwist χ j where
  toFun x := ⟨ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) x.val⟩
  map_smul' g x :=
    ZModTwist.ext (by simp only [val_smul, map_mul, castHom_charScalar χ h, MonoidHom.id_apply])
  map_zero' := ZModTwist.ext (by simp only [val_zero, map_zero])
  map_add' x y := ZModTwist.ext (by simp only [val_add, map_add])

@[simp]
theorem val_reduce {j : ℕ} (h : j ≤ i) (x : ZModTwist χ i) :
    (reduce χ h x).val = ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ j)) x.val :=
  (rfl)

theorem reduce_surjective {j : ℕ} (h : j ≤ i) : Function.Surjective (reduce χ h) := fun y ↦ by
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow p h) y.val
  exact ⟨⟨x⟩, ZModTwist.ext hx⟩

end ZModTwist

/-! ### The prescription property -/

/-- **The prescription property** of a continuous character `χ : G →ₜ* ℤ_pˣ` (Labute's condition
on the orientation of a Demushkin group): every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`, for
`i ≥ 1`, is surjective. In cocycle terms, every continuous crossed homomorphism `G → I(χ)/p` is,
modulo principal ones, the reduction of a continuous crossed homomorphism `G → I(χ)/pⁱ`. -/
def HasPrescriptionProperty (χ : G →ₜ* ℤ_[p]ˣ) : Prop :=
  ∀ (i : ℕ) (hi : 1 ≤ i),
    Function.Surjective
      (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi) continuous_of_discreteTopology)

/-- **Every continuous character of a free pro-`p` group has the prescription property.** A
continuous `1`-cocycle `F → I(χ)/p` is determined by its values on the generators, each of which
lifts to `I(χ)/pⁱ`, and a continuous `1`-cocycle `F → I(χ)/pⁱ` with those lifted values exists;
its reduction agrees with the given cocycle on the generators, hence everywhere. -/
theorem freeProP.hasPrescriptionProperty {X : Type u} (χ : freeProP p X →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ := by
  intro i hi y
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    -- Lift the values of `c` on the generators from `I(χ)/p` to `I(χ)/pⁱ`.
    choose v hv using fun x : X ↦
      ZModTwist.reduce_surjective χ hi ((c : freeProP p X → ZModTwist χ 1) (freeProP.of x))
    obtain ⟨c', hc', hc'v⟩ :=
      freeProP.exists_mem_Z1_forall_apply_of_eq (ZModTwist.isProP_multiplicative χ i) v
    refine ⟨((⟨c', hc'⟩ : Z1 (freeProP p X) (ZModTwist χ i)) : H1 _ _), ?_⟩
    rw [explicitCoeff1_mk]
    congr 1
    -- The reduction of `c'` and `c` are continuous cocycles agreeing on the generators.
    refine Subtype.ext (freeProP.eq_of_mem_Z1_of_forall_of (Subtype.property _) c.2 fun x ↦ ?_)
    exact (cocyclesMap1_apply _ _ _ _ _ _ _ _ ⟨c', hc'⟩ (freeProP.of x)).trans (by simp [hc'v, hv])

end TauCeti
