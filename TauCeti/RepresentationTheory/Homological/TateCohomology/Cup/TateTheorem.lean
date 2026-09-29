/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.TrivialInt
public import TauCeti.RepresentationTheory.Homological.TateCohomology.IsoCriterion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic

/-!
# Tate's theorem: cup product with a degree-two class

Let `G` be a finite group, `N` a representation of `G` over `ℤ` and `u ∈ Ĥ²(G, N)` a class
which generates `Ĥ²(G, N)`, a group of order `|G|`. Suppose that for every subgroup `S` of `G` of
prime-power order, `Ĥ¹(S, N) = 0` and `Ĥ²(S, N)` has order `|S|`. Then cup product with `u` is
a bijection `Ĥʳ(G, ℤ) → Ĥʳ⁺²(G, ℤ ⊗ N)` in every integer degree `r`
(`TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup`). This is Tate's theorem (J. Tate,
*The higher dimensional cohomology groups of class field theory*, Ann. of Math. 56, 1952), in
the form used to derive the reciprocity isomorphisms of class field theory.

The classical statement also asks that the restriction of `u` to each subgroup `S` generate
`Ĥ²(S, N)`. That hypothesis is not needed: corestriction after restriction is multiplication by
the index, so the restricted class already has order `|S|` in a group of order `|S|`. The proof
here makes exactly this observation, in degree zero after dimension shifting.

## Proof

The cup product with a degree-two class is not induced by a morphism of representations, but
after two upward dimension shifts it is: writing `N₂` for the twice-shifted representation,
`u` corresponds to the class of an invariant `a ∈ Ĥ⁰(G, N₂)`, and cup product with `u` is, up to
the dimension-shifting isomorphisms, the map induced on Tate cohomology by `ℤ ⟶ ℤ ⊗ N₂`,
`1 ↦ 1 ⊗ a` (`cup_dimensionShiftUpTwoIso_hom`). Tate's isomorphism criterion for a morphism of
representations (`TauCeti.TateCohomology.map_bijective_of_forall_isPGroup`) then reduces the
theorem to the three degrees `-1`, `0`, `1` on subgroups of prime-power order. In degree `-1` the
target vanishes because `Ĥ¹(S, N) = 0`, in degree `1` the source `Ĥ¹(S, ℤ)` vanishes, and in
degree `0` the map `Ĥ⁰(S, ℤ) → Ĥ⁰(S, ℤ ⊗ N₂)` is a bijection between groups of order `|S|` by
the corestriction argument above.

## Main statements

* `TauCeti.TateCohomology.dimensionShiftUpTwoIso`: two upward dimension shifts,
  `Ĥ⁰(G, N₂) ≅ Ĥ²(G, N)`.
* `TauCeti.TateCohomology.cup_dimensionShiftUpTwoIso_hom`: cup product with a class shifted
  twice is the degree-zero cup product, shifted twice.
* `TauCeti.TateCohomology.trivialResIso`: Tate cohomology of the trivial integral representation
  of a subgroup, as Tate cohomology of the restricted trivial representation.
* `TauCeti.TateCohomology.map_res_zero_bijective_of_injective`: the degree-zero step on a
  subgroup, by the corestriction argument.
* `TauCeti.TateCohomology.cup_bijective_of_cupTrivialInt_bijective`,
  `TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup`: Tate's theorem, with the degree-zero
  bijection respectively the generation and order of `Ĥ²(G, N)` as hypothesis.

## References

* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. 56
  (1952), 294–297.
* E. Artin and J. Tate, *Class Field Theory*, Preliminaries §2, Theorem A, and Chapter XIV §4,
  Theorem 1.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §10.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

section DimensionShift

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Two upward dimension shifts identify degree-zero Tate cohomology of the twice-shifted
representation with degree-two Tate cohomology of the representation itself. -/
def dimensionShiftUpTwoIso (N : Rep k G) :
    tateCohomology (dimensionShiftUp (dimensionShiftUp N)) 0 ≅ tateCohomology N 2 :=
  dimensionShiftUpIso (dimensionShiftUp N) 0 ≪≫ dimensionShiftUpIso N 1

/-- The double shift is the composite of the two upward dimension shifts. -/
theorem dimensionShiftUpTwoIso_hom (N : Rep k G) :
    (dimensionShiftUpTwoIso N).hom =
      (dimensionShiftUpIso (dimensionShiftUp N) 0).hom ≫ (dimensionShiftUpIso N 1).hom := by
  rw [dimensionShiftUpTwoIso, Iso.trans_hom]

/-- Cup product with a degree-two class obtained by shifting a degree-zero class `z` twice is the
degree-zero cup product with `z`, followed by the two tensored dimension shifts. The two signs
`(-1)^p` of the shifting rule cancel. -/
theorem cup_dimensionShiftUpTwoIso_hom (M N : Rep k G) (p : ℤ) (x : tateCohomology M p)
    (z : tateCohomology (dimensionShiftUp (dimensionShiftUp N)) 0) :
    cup M N p 2 (p + 2) rfl x ((dimensionShiftUpTwoIso N).hom z) =
      (tensorDimensionShiftUpIso N M (p + 1) (p + 2) (by omega)).hom
        ((tensorDimensionShiftUpIso (dimensionShiftUp N) M p (p + 1) rfl).hom
          (cupH0 M (dimensionShiftUp (dimensionShiftUp N)) p x z)) := by
  -- The first shift, in bidegree `(p, 0 + 1)`; `0 + 1` is `1` by definition.
  have h₁ : cup M (dimensionShiftUp N) p 1 (p + 1) rfl x
        ((dimensionShiftUpIso (dimensionShiftUp N) 0).hom z) =
      p.negOnePow • (tensorDimensionShiftUpIso (dimensionShiftUp N) M p (p + 1) rfl).hom
        (cupH0 M (dimensionShiftUp (dimensionShiftUp N)) p x z) := by
    refine (cup_dimensionShiftUpIso_hom M (dimensionShiftUp N) le_rfl (add_zero p) rfl x
      z).trans ?_
    rw [cup_zero_right]
  -- The second shift, in bidegree `(p, 1 + 1)`; `1 + 1` is `2` by definition.
  have h₂ := cup_dimensionShiftUpIso_hom M N (q := 1) (r := p + 2) zero_le_one rfl (by omega) x
    ((dimensionShiftUpIso (dimensionShiftUp N) 0).hom z)
  rw [dimensionShiftUpTwoIso_hom, ModuleCat.comp_apply]
  refine h₂.trans ?_
  rw [h₁, map_zsmul_unit, negOnePow_smul_negOnePow_smul]

end DimensionShift

section Subgroup

variable {G : Type} [Group G] [Finite G]

attribute [local instance] Subgroup.fintypeOfFinite

/-! ### Trivial integral coefficients on a subgroup -/

omit [Finite G] in
/-- The identity of `ℤ` intertwines the trivial representation of a subgroup `S` of `G` with the
restriction to `S` of the trivial representation of `G`. -/
theorem isIntertwiningMap_trivial_res (S : Subgroup G) :
    (Rep.trivial ℤ S ℤ).ρ.IsIntertwiningMap
      ((Rep.res S.subtype (Rep.trivial ℤ G ℤ)).ρ.comp ((MulEquiv.refl S : S ≃* S) : S →* S))
      (LinearEquiv.refl ℤ ℤ) :=
  ⟨fun _ _ ↦ rfl⟩

/-- Tate cohomology of the trivial integral representation of a subgroup `S` of `G`, identified
with Tate cohomology of the restriction to `S` of the trivial integral representation of `G`. -/
def trivialResIso (S : Subgroup G) (n : ℤ) :
    tateCohomology (Rep.trivial ℤ S ℤ) n ≅
      tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) n :=
  mapIso (e := MulEquiv.refl S) (e' := LinearEquiv.refl ℤ ℤ) (isIntertwiningMap_trivial_res S) n

/-- The comparison `trivialResIso` is the Tate map attached to the compatible pair
`isIntertwiningMap_trivial_res`. -/
theorem trivialResIso_hom (S : Subgroup G) (n : ℤ) :
    (trivialResIso S n).hom =
      map (e := MulEquiv.refl S) (isIntertwiningMap_trivial_res S) n := by
  rw [trivialResIso, mapIso_hom]

/-- Degree-zero Tate cohomology of the restricted trivial integral representation has the order
of the subgroup. -/
theorem natCard_tateCohomology_zero_res_trivial_int_eq_card (S : Subgroup G) :
    Nat.card (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 0) = Nat.card S :=
  (Nat.card_congr (trivialResIso S 0).toLinearEquiv.toEquiv).symm.trans
    (natCard_tateCohomology_zero_trivial_int_eq_card S)

/-- Degree-one Tate cohomology of the restricted trivial integral representation vanishes: it is
`H¹(S, ℤ) = Hom(S, ℤ) = 0`. -/
theorem isZero_tateCohomology_one_res_trivial_int (S : Subgroup G) :
    IsZero (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
  ((TauCeti.groupCohomology.isZero_H1_of_isTrivial (Rep.trivial ℤ S ℤ)).of_iso
    ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ S ℤ))).of_iso
      (trivialResIso S 1).symm

/-- The invariant `1` of the restricted trivial integral representation. -/
private def resTrivialOne (S : Subgroup G) :
    (Rep.res S.subtype (Rep.trivial ℤ G ℤ)).ρ.invariants :=
  ⟨1, fun _ ↦ rfl⟩

/-- Every degree-zero class of the restricted trivial integral representation is an integer
multiple of the class of `1`. -/
private theorem exists_eq_zsmul_H0π_resTrivialOne (S : Subgroup G)
    (x : tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 0) :
    ∃ n : ℤ, x = n • H0π _ (resTrivialOne S) := by
  induction x using H0_induction_on with
  | h y =>
    refine ⟨(y : ℤ), ?_⟩
    have hy : y = (y : ℤ) • resTrivialOne S := Subtype.ext (by simp [resTrivialOne])
    conv_lhs => rw [hy]
    rw [map_zsmul]

/-- The order of the subgroup kills the class of `1`. -/
private theorem natCard_zsmul_H0π_resTrivialOne (S : Subgroup G) :
    (Nat.card S : ℤ) • H0π _ (resTrivialOne S) = 0 := by
  rw [← map_zsmul]
  refine (H0π_eq_zero_iff _).2 ⟨1, ?_⟩
  simp [Representation.norm, resTrivialOne, Nat.card_eq_fintype_card]

end Subgroup

section TateTheorem

variable {G : Type} [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-! ### The degree-zero step on a subgroup -/

/-- The degree-zero step of Tate's theorem on a subgroup `S`. Let `f : ℤ ⟶ B` be a morphism from
the trivial integral representation which is injective on `Ĥ⁰(G, ℤ) → Ĥ⁰(G, B)`, and suppose
`Ĥ⁰(S, B)` has order `|S|`. Then `f` is bijective on `Ĥ⁰(S, ℤ) → Ĥ⁰(S, B)`: the image of the
class of `1` on `S` is the restriction of the image of the class of `1` on `G`, which has order
`|G|`, and corestriction after restriction is multiplication by `[G : S]`, so the restricted class
has order `|S|` in a group of order `|S|`. -/
theorem map_res_zero_bijective_of_injective {B : Rep ℤ G} (f : Rep.trivial ℤ G ℤ ⟶ B)
    (hinj : Function.Injective ((tateCohomologyFunctor 0).map f)) (S : Subgroup G)
    (hcard : Nat.card (tateCohomology (Rep.res S.subtype B) 0) = Nat.card S) :
    Function.Bijective ((tateCohomologyFunctor 0).map ((resFunctor S.subtype).map f)) := by
  -- The invariant `1` of the trivial representation of `G`.
  let one : (Rep.trivial ℤ G ℤ).ρ.invariants := ⟨1, fun _ ↦ rfl⟩
  -- The image of the class of `1` on `S` is the restriction of the image of the class of `1`.
  have hy : (tateCohomologyFunctor 0).map ((resFunctor S.subtype).map f)
        (H0π _ (resTrivialOne S)) =
      H0Res B S ((tateCohomologyFunctor 0).map f (H0π _ one)) := by
    rw [H0π_comp_tateCohomologyFunctor_map_apply, H0π_comp_tateCohomologyFunctor_map_apply,
      H0π_comp_H0Res_apply]
    -- Both sides are the class of the invariant `f 1`, viewed as an invariant of `S`.
    rfl
  -- If `n` kills the image of the class of `1` on `S`, then `|S|` divides `n`.
  have key : ∀ n : ℤ, n • (tateCohomologyFunctor 0).map ((resFunctor S.subtype).map f)
      (H0π _ (resTrivialOne S)) = 0 → (Nat.card S : ℤ) ∣ n := by
    intro n hn
    rw [hy, ← map_zsmul] at hn
    have hcor := congrArg (H0Cor B S) hn
    rw [H0Cor_comp_H0Res_apply, map_zero, ← natCast_zsmul, smul_smul, ← map_zsmul] at hcor
    have h0 := hinj (hcor.trans (map_zero _).symm)
    have hz := congrArg (H0LinearEquivTrivialIntZModCard G) h0
    rw [map_zsmul, H0LinearEquivTrivialIntZModCard_H0π, map_zero, zsmul_eq_mul] at hz
    simp only [one, Int.cast_one, mul_one, ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← S.index_mul_card, Nat.cast_mul] at hz
    exact (mul_dvd_mul_iff_left (Nat.cast_ne_zero.2 S.index_ne_zero_of_finite)).1 hz
  have hinjS : Function.Injective
      ((tateCohomologyFunctor 0).map ((resFunctor S.subtype).map f)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨n, rfl⟩ := exists_eq_zsmul_H0π_resTrivialOne S x
    rw [map_zsmul] at hx
    obtain ⟨c, rfl⟩ := key n hx
    rw [mul_comm, mul_smul, natCard_zsmul_H0π_resTrivialOne, zsmul_zero]
  have : Finite (tateCohomology (Rep.res S.subtype B) 0) :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne Nat.card_pos.ne')
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨hinjS, (natCard_tateCohomology_zero_res_trivial_int_eq_card S).trans hcard.symm⟩

/-- Tate cohomology on a subgroup of the tensor product of the trivial representation with the
twice-shifted `N`, in degree `n`, is Tate cohomology of `N` on that subgroup in degree `n + 2`. -/
private def resTensorDimensionShiftUpTwoIso (N : Rep ℤ G) (S : Subgroup G) (n : ℤ) :
    tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ ⊗ dimensionShiftUp (dimensionShiftUp N)))
        n ≅
      tateCohomology (Rep.res S.subtype N) (n + 1 + 1) :=
  (tateCohomologyFunctor n).mapIso
      ((resFunctor S.subtype).mapIso (λ_ (dimensionShiftUp (dimensionShiftUp N)))) ≪≫
    dimensionShiftUpResIso (dimensionShiftUp N) S n ≪≫ dimensionShiftUpResIso N S (n + 1)

/-! ### Tate's theorem -/

/-- **Tate's theorem**, with the degree-zero bijection as hypothesis. Let `G` be a finite group,
`N` a representation of `G` over `ℤ` and `u ∈ Ĥ²(G, N)`. Suppose that

* cup product with `u` is a bijection `Ĥ⁰(G, ℤ) → Ĥ²(G, N)`;
* for every subgroup `S` of `G` of prime-power order, `Ĥ¹(S, N) = 0` and `Ĥ²(S, N)` has order
  `|S|`.

Then cup product with `u` is a bijection `Ĥʳ(G, ℤ) → Ĥʳ⁺²(G, ℤ ⊗ N)` in every integer degree
`r`. -/
theorem cup_bijective_of_cupTrivialInt_bijective (N : Rep ℤ G) (u : tateCohomology N 2)
    (hbij : Function.Bijective (cupTrivialInt N u))
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (Rep.res S.subtype N) 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Nat.card (tateCohomology (Rep.res S.subtype N) 2) = Nat.card S)
    (r r' : ℤ) (h : r + 2 = r') :
    Function.Bijective fun x : tateCohomology (Rep.trivial ℤ G ℤ) r ↦
      cup (Rep.trivial ℤ G ℤ) N r 2 r' h x u := by
  subst h
  -- `u` is the double shift of the class of an invariant `a` of the twice-shifted `N`.
  obtain ⟨a, ha⟩ := H0_induction_on
    (C := fun z ↦ ∃ a, H0π (dimensionShiftUp (dimensionShiftUp N)) a = z)
    ((dimensionShiftUpTwoIso N).inv u) fun y ↦ ⟨y, rfl⟩
  have hu : u = (dimensionShiftUpTwoIso N).hom (H0π _ a) := by
    rw [ha, Iso.inv_hom_id_apply]
  set f := Rep.tensorInvariant (Rep.trivial ℤ G ℤ) a with hf
  -- In every degree, cup product with `u` is the map induced by `f`, followed by isomorphisms.
  have hcup : ∀ p : ℤ,
      (fun x : tateCohomology (Rep.trivial ℤ G ℤ) p ↦
        cup (Rep.trivial ℤ G ℤ) N p 2 (p + 2) rfl x u) =
      ⇑(tensorDimensionShiftUpIso N (Rep.trivial ℤ G ℤ) (p + 1) (p + 2) (by omega)).hom ∘
        ⇑(tensorDimensionShiftUpIso (dimensionShiftUp N) (Rep.trivial ℤ G ℤ) p (p + 1) rfl).hom ∘
        ⇑((tateCohomologyFunctor p).map f) := fun p ↦ funext fun x ↦ by
    rw [hu, cup_dimensionShiftUpTwoIso_hom, cupH0_H0π]
    -- Unfold the function composition.
    rfl
  -- In degree zero on `G`, cup product with `u` is bijective, so the map induced by `f` is
  -- injective there.
  have hinj : Function.Injective ((tateCohomologyFunctor 0).map f) := by
    have : ⇑(cupTrivialInt N u) = ⇑((tateCohomologyFunctor 2).map (λ_ N).hom) ∘
        fun x : tateCohomology (Rep.trivial ℤ G ℤ) 0 ↦
          cup (Rep.trivial ℤ G ℤ) N 0 2 (0 + 2) rfl x u :=
      funext fun x ↦ cupTrivialInt_apply N u x
    rw [this, hcup 0] at hbij
    exact hbij.injective.of_comp.of_comp.of_comp
  rw [hcup r]
  refine (ConcreteCategory.bijective_of_isIso _).comp
    ((ConcreteCategory.bijective_of_isIso _).comp ?_)
  -- The three hypotheses of the criterion quantify over an arbitrary `Fintype` structure on `S`,
  -- which is replaced by the one attached to the finiteness of `G`.
  refine map_bijective_of_forall_isPGroup f (q := 0) ?_ ?_ ?_ r
  · -- Degree `-1`: the target `Ĥ⁻¹(S, ℤ ⊗ N₂) ≅ Ĥ¹(S, N)` vanishes.
    intro p _ S inst hS
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    have : Subsingleton (tateCohomology
        (Rep.res S.subtype (Rep.trivial ℤ G ℤ ⊗ dimensionShiftUp (dimensionShiftUp N))) (0 - 1)) :=
      ModuleCat.subsingleton_of_isZero
        ((h1 p S hS).of_iso (resTensorDimensionShiftUpTwoIso N S (0 - 1)))
    exact Function.surjective_to_subsingleton _
  · -- Degree `0`: the corestriction argument, with `Ĥ⁰(S, ℤ ⊗ N₂) ≅ Ĥ²(S, N)` of order `|S|`.
    intro p _ S inst hS
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    exact map_res_zero_bijective_of_injective f hinj S
      ((Nat.card_congr (resTensorDimensionShiftUpTwoIso N S 0).toLinearEquiv.toEquiv).trans
        (hcard p S hS))
  · -- Degree `1`: the source `Ĥ¹(S, ℤ)` vanishes.
    intro p _ S inst hS
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    have : Subsingleton (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) (0 + 1)) :=
      ModuleCat.subsingleton_of_isZero (isZero_tateCohomology_one_res_trivial_int S)
    exact Function.injective_of_subsingleton _

/-- **Tate's theorem.** Let `G` be a finite group, `N` a representation of `G` over `ℤ` and
`u ∈ Ĥ²(G, N)`. Suppose that

* `u` generates `Ĥ²(G, N)`, a group of order `|G|`;
* for every subgroup `S` of `G` of prime-power order, `Ĥ¹(S, N) = 0` and `Ĥ²(S, N)` has order
  `|S|`.

Then cup product with `u` is a bijection `Ĥʳ(G, ℤ) → Ĥʳ⁺²(G, ℤ ⊗ N)` in every integer degree
`r`. The classical hypothesis that the restriction of `u` to each subgroup generates its `Ĥ²` is
a consequence of these and is not assumed. -/
theorem cup_bijective_of_forall_isPGroup (N : Rep ℤ G) (u : tateCohomology N 2)
    (hgen : ∀ y : tateCohomology N 2, ∃ m : ℤ, m • u = y)
    (hcardG : Nat.card (tateCohomology N 2) = Nat.card G)
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (Rep.res S.subtype N) 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Nat.card (tateCohomology (Rep.res S.subtype N) 2) = Nat.card S)
    (r r' : ℤ) (h : r + 2 = r') :
    Function.Bijective fun x : tateCohomology (Rep.trivial ℤ G ℤ) r ↦
      cup (Rep.trivial ℤ G ℤ) N r 2 r' h x u :=
  cup_bijective_of_cupTrivialInt_bijective N u
    (cupTrivialInt_bijective N u hgen (hcardG.trans Nat.card_eq_fintype_card)) h1 hcard r r' h

end TateTheorem

end TauCeti.TateCohomology
