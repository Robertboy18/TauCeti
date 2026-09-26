/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.DegreeZero
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift

/-!
# The Tate cup product in all bidegrees

For a finite group `G` and representations `M`, `N`, this file constructs the cup product

`tateCohomology M p × tateCohomology N q → tateCohomology (M ⊗ N) r`, `r = p + q`,

for all integers `p` and `q`, as a `k`-bilinear map. It extends the product `cupH0` with a
degree-zero class by dimension shifting in the second variable (Cassels–Fröhlich, Chapter IV, §7;
Brown, Chapter VI, §5). Writing `δ` for the connecting maps of the dimension-shifting sequences
`0 → N → Coind_⊥^G N → dimensionShiftUp N → 0` and `0 → dimensionShiftDown N → Ind_⊥^G N → N → 0`,
which are isomorphisms on Tate cohomology, and also for the connecting maps of the same sequences
tensored on the left with `M`, the product is determined by its value `cupH0` on degree-zero
classes and by the rule

`x ∪ δ y = (-1)^p δ (x ∪ y)` for `x` of degree `p`.

The sign is the standard one for a bigraded product compatible with connecting homomorphisms in
the second variable. For `q ≥ 0` the rule is applied upwards, with the upward shift of `N`, and for
`q < 0` downwards, with the downward shift of `N`; in each range the rule holds by construction
(`cup_dimensionShiftUpIso_hom`, `cup_dimensionShiftDownIso_hom`). That the rule holds for every
`k`-split short exact sequence in the second variable, the compatibility with connecting maps in
the first variable, associativity, graded commutativity and the compatibility with restriction are
the further properties of the product; they are not proved here.

The target degree of `cup` is a parameter `r` together with a proof of `p + q = r`, in the style of
Mathlib's `ShortComplex.ShortExact.δ`, so that neither the definition nor its consumers need to
transport classes along equalities of degrees.

## Main definitions

* `TauCeti.TateCohomology.cup`: the cup product
  `tateCohomology M p →ₗ[k] tateCohomology N q →ₗ[k] tateCohomology (M ⊗ N) r` for `p + q = r`.

## Main statements

* `TauCeti.TateCohomology.cup_zero_right`: in bidegree `(p, 0)` the product is `cupH0`.
* `TauCeti.TateCohomology.cup_dimensionShiftUpIso_hom`,
  `TauCeti.TateCohomology.cup_dimensionShiftDownIso_hom`: the defining rule
  `x ∪ δ y = (-1)^p δ (x ∪ y)` for the upward shift when the second degree is nonnegative, and for
  the downward shift when it is negative.
* `TauCeti.TateCohomology.cup_map_left`: naturality in the first coefficient representation.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- `addNat p n = p + n`, by recursion on `n`, so that `addNat p 0` is `p` and `addNat p (n + 1)` is
`addNat p n + 1` definitionally. It indexes the target degrees of the recursion defining the cup
product with a class of nonnegative degree, whose base case is `cupH0`, landing in degree `p`. -/
private def addNat (p : ℤ) : ℕ → ℤ
  | 0 => p
  | n + 1 => addNat p n + 1

private theorem addNat_succ (p : ℤ) (n : ℕ) : addNat p (n + 1) = addNat p n + 1 :=
  rfl

private theorem addNat_eq (p : ℤ) (n : ℕ) : addNat p n = p + n := by
  induction n with
  | zero => simp [addNat]
  | succ n ih => simp [addNat, ih, add_assoc]

variable (M : Rep k G)

/-- The cup product with a class of nonnegative second degree `n`, by recursion on `n`: for `n = 0`
it is `cupH0`, and for `y` of degree `n + 1` it is `x ∪ y = (-1)^p δ (x ∪ δ⁻¹ y)`, with `δ⁻¹ y` in
degree `n` of the upward shift of `N`. -/
private def cupNonneg (p : ℤ) : (n : ℕ) → (N : Rep k G) →
    tateCohomology M p →ₗ[k] tateCohomology N n →ₗ[k] tateCohomology (M ⊗ N) (addNat p n)
  | 0, N => cupH0 M N p
  | n + 1, N => p.negOnePow •
      (((cupNonneg p n (dimensionShiftUp N)).compr₂
        (tensorDimensionShiftUpIso N M (addNat p n) (addNat p (n + 1))
          (addNat_succ p n).symm).hom.hom).compl₂ (dimensionShiftUpIso N n).inv.hom)

/-- The cup product with a class of negative second degree `-(n + 1)`, by recursion on `n`: for `y`
of degree `-(n + 1)` it is `x ∪ y = (-1)^p δ⁻¹ (x ∪ δ y)`, with `δ y` in degree `-n` of the
downward shift of `N`. -/
private def cupNeg (p : ℤ) : (n : ℕ) → (N : Rep k G) →
    tateCohomology M p →ₗ[k] tateCohomology N (Int.negSucc n) →ₗ[k]
      tateCohomology (M ⊗ N) (p - (n + 1 : ℕ))
  | 0, N => p.negOnePow •
      (((cupH0 M (dimensionShiftDown N) p).compr₂
        (tensorDimensionShiftDownIso N M (p - ((0 + 1 : ℕ) : ℤ)) p (by simp)).inv.hom).compl₂
          (dimensionShiftDownIso N (Int.negSucc 0)).hom.hom)
  | n + 1, N => p.negOnePow •
      (((cupNeg p n (dimensionShiftDown N)).compr₂
        (tensorDimensionShiftDownIso N M (p - ((n + 1 + 1 : ℕ) : ℤ)) (p - ((n + 1 : ℕ) : ℤ))
          (by push_cast; ring)).inv.hom).compl₂
            (dimensionShiftDownIso N (Int.negSucc (n + 1))).hom.hom)

variable (N : Rep k G)

/-- **The Tate cup product** `Ĥᵖ(G, M) × Ĥ^q(G, N) → Ĥʳ(G, M ⊗ N)` for `p + q = r`, in all integer
bidegrees, as a `k`-bilinear map. In bidegree `(p, 0)` it is `cupH0` (`cup_zero_right`), and it is
determined from there by the rule `x ∪ δ y = (-1)^p δ (x ∪ y)` for the connecting maps of the
dimension-shifting sequences of `N` and of their tensor products with `M`
(`cup_dimensionShiftUpIso_hom`, `cup_dimensionShiftDownIso_hom`). -/
def cup (p q r : ℤ) (h : p + q = r) :
    tateCohomology M p →ₗ[k] tateCohomology N q →ₗ[k] tateCohomology (M ⊗ N) r :=
  match q, h with
  | .ofNat n, h => (cupNonneg M p n N).compr₂
      (eqToHom (congrArg (tateCohomology (M ⊗ N)) ((addNat_eq p n).trans h))).hom
  | .negSucc n, h => (cupNeg M p n N).compr₂
      (eqToHom (congrArg (tateCohomology (M ⊗ N)) (by rw [Int.negSucc_eq] at h; omega))).hom

/-!
The unfolding lemmas below are stated with the target degree in the form in which the recursion
produces it, so that the transport along an equality of degrees in the definition of `cup` is
along a reflexivity proof and disappears definitionally.
-/

private theorem cup_natCast (p : ℤ) (n : ℕ) (h : p + n = addNat p n) :
    cup M N p n (addNat p n) h = cupNonneg M p n N :=
  rfl

private theorem cup_natCast_add_one (p : ℤ) (n : ℕ) (h : p + (n + 1) = addNat p (n + 1)) :
    cup M N p (n + 1) (addNat p (n + 1)) h = cupNonneg M p (n + 1) N :=
  rfl

private theorem cup_negSucc (p : ℤ) (n : ℕ) (h : p + Int.negSucc n = p - (n + 1 : ℕ)) :
    cup M N p (Int.negSucc n) (p - (n + 1 : ℕ)) h = cupNeg M p n N :=
  rfl

private theorem cup_negSucc_zero_add_one (p : ℤ) (h : p + (Int.negSucc 0 + 1) = p) :
    cup M N p (Int.negSucc 0 + 1) p h = cupH0 M N p :=
  rfl

private theorem cup_negSucc_succ_add_one (p : ℤ) (n : ℕ)
    (h : p + (Int.negSucc (n + 1) + 1) = p - (n + 1 : ℕ)) :
    cup M N p (Int.negSucc (n + 1) + 1) (p - (n + 1 : ℕ)) h = cupNeg M p n N :=
  rfl

private theorem cupNonneg_succ_apply (p : ℤ) (n : ℕ) (x : tateCohomology M p)
    (y : tateCohomology N (n + 1 : ℕ)) :
    cupNonneg M p (n + 1) N x y =
      p.negOnePow • (tensorDimensionShiftUpIso N M (addNat p n) (addNat p (n + 1))
        (addNat_succ p n).symm).hom
          (cupNonneg M p n (dimensionShiftUp N) x ((dimensionShiftUpIso N n).inv y)) :=
  rfl

private theorem cupNeg_zero_apply (p : ℤ) (x : tateCohomology M p)
    (y : tateCohomology N (Int.negSucc 0)) :
    cupNeg M p 0 N x y =
      p.negOnePow • (tensorDimensionShiftDownIso N M (p - ((0 + 1 : ℕ) : ℤ)) p (by simp)).inv
        (cupH0 M (dimensionShiftDown N) p x ((dimensionShiftDownIso N (Int.negSucc 0)).hom y)) :=
  rfl

private theorem cupNeg_succ_apply (p : ℤ) (n : ℕ) (x : tateCohomology M p)
    (y : tateCohomology N (Int.negSucc (n + 1))) :
    cupNeg M p (n + 1) N x y =
      p.negOnePow • (tensorDimensionShiftDownIso N M (p - ((n + 1 + 1 : ℕ) : ℤ))
        (p - ((n + 1 : ℕ) : ℤ)) (by push_cast; ring)).inv
          (cupNeg M p n (dimensionShiftDown N) x
            ((dimensionShiftDownIso N (Int.negSucc (n + 1))).hom y)) :=
  rfl

-- This is the case `n = 0` of `cup_natCast`: `((0 : ℕ) : ℤ)` is `0`, `addNat p 0` is `p` and
-- `cupNonneg M p 0 N` is `cupH0 M N p`, each by definition.
/-- In bidegree `(p, 0)` the cup product is the product `cupH0` with a degree-zero class. -/
@[simp]
theorem cup_zero_right (p : ℤ) (h : p + 0 = p) : cup M N p 0 p h = cupH0 M N p :=
  cup_natCast M N p 0 h

/-- **The defining rule of the cup product for the upward dimension shift**: for `x` of degree `p`
and `y` of nonnegative degree `q` in `dimensionShiftUp N`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the
first `δ` is the shift `Ĥ^q(G, dimensionShiftUp N) ≅ Ĥ^(q+1)(G, N)` and the second is its tensor
product with `M`. -/
theorem cup_dimensionShiftUpIso_hom {p q r' r : ℤ} (hq : 0 ≤ q) (h' : p + q = r')
    (h : r' + 1 = r) (x : tateCohomology M p) (y : tateCohomology (dimensionShiftUp N) q) :
    cup M N p (q + 1) r (by omega) x ((dimensionShiftUpIso N q).hom y) =
      p.negOnePow • (tensorDimensionShiftUpIso N M r' r h).hom
        (cup M (dimensionShiftUp N) p q r' h' x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain rfl : r' = addNat p n := by rw [addNat_eq]; omega
  obtain rfl : r = addNat p (n + 1) := by rw [addNat_eq]; push_cast; omega
  rw [cup_natCast_add_one, cup_natCast, cupNonneg_succ_apply, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply]

/-- **The defining rule of the cup product for the downward dimension shift**: for `x` of degree
`p` and `y` of negative degree `q` in `N`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the first `δ` is the
shift `Ĥ^q(G, N) ≅ Ĥ^(q+1)(G, dimensionShiftDown N)` and the second is its tensor product with
`M`. -/
theorem cup_dimensionShiftDownIso_hom {p q r' r : ℤ} (hq : q < 0) (h' : p + q = r')
    (h : r' + 1 = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    cup M (dimensionShiftDown N) p (q + 1) r (by omega) x ((dimensionShiftDownIso N q).hom y) =
      p.negOnePow • (tensorDimensionShiftDownIso N M r' r h).hom (cup M N p q r' h' x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
  obtain rfl : r' = p - (n + 1 : ℕ) := by rw [Int.negSucc_eq] at h'; omega
  cases n with
  | zero =>
    obtain rfl : r = p := by simp at h; omega
    rw [cup_negSucc_zero_add_one, cup_negSucc, cupNeg_zero_apply, Units.smul_def, Units.smul_def,
      map_zsmul, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
      ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  | succ n =>
    obtain rfl : r = p - (n + 1 : ℕ) := by push_cast at h ⊢; omega
    rw [cup_negSucc_succ_add_one, cup_negSucc, cupNeg_succ_apply, Units.smul_def, Units.smul_def,
      map_zsmul, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
      ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

variable {M N}

/-- The cup product is natural in the first coefficient representation. -/
theorem cup_map_left {M' : Rep k G} (f : M ⟶ M') (p q r : ℤ) (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q) :
    cup M' N p q r h ((tateCohomologyFunctor p).map f x) y =
      (tateCohomologyFunctor r).map (f ▷ N) (cup M N p q r h x y) := by
  rcases le_or_gt 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain rfl : r = addNat p n := by rw [addNat_eq]; omega
    rw [cup_natCast, cup_natCast]
    clear h hq
    induction n generalizing N with
    | zero => exact cupH0_map_left f p x y
    | succ n ih =>
      rw [cupNonneg_succ_apply, cupNonneg_succ_apply, ih, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftUpIso_hom_naturality]
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    obtain rfl : r = p - (n + 1 : ℕ) := by rw [Int.negSucc_eq] at h; omega
    rw [cup_negSucc, cup_negSucc]
    clear h hq
    induction n generalizing N with
    | zero =>
      rw [cupNeg_zero_apply, cupNeg_zero_apply, cupH0_map_left, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftDownIso_inv_naturality]
    | succ n ih =>
      rw [cupNeg_succ_apply, cupNeg_succ_apply, ih, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftDownIso_inv_naturality]

end TauCeti.TateCohomology
