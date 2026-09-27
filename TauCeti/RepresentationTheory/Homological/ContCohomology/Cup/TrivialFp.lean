/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.GradedComm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp

/-!
# The cup square on `H¹(G, 𝔽_p)`

For a topological group `G` and a natural number `p`, `TauCeti.trivialFp p G` is the trivial
representation of `G` on `ZMod p`, and `TauCeti.cohomFp p G n` is its continuous cohomology
`Hⁿ(G, 𝔽_p)`. Multiplication in `ZMod p` is `ZMod p`-bilinear, jointly continuous because the
coefficients are discrete, and equivariant because the action is trivial, so it is a coefficient
pairing `TauCeti.fpPairing p G` of `trivialFp p G` with itself. Its cup product in bidegree
`(1, 1)` is the **cup square**

```text
cupFp p G : H¹(G, 𝔽_p) →ₗ[𝔽_p] H¹(G, 𝔽_p) →ₗ[𝔽_p] H²(G, 𝔽_p),
```

the pairing whose nondegeneracy defines Demushkin groups. Because multiplication is commutative the
opposite pairing of `fpPairing p G` is itself, and graded commutativity of the cup product in
bidegree `(1, 1)` reads `cupFp p G a b = - cupFp p G b a` (`TauCeti.cupFp_gradedComm`).

## Main definitions

* `TauCeti.fpPairing`: multiplication in `ZMod p` as a coefficient pairing of `trivialFp p G`
  with itself.
* `TauCeti.cupFp`: the cup square `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)`.

## Main results

* `TauCeti.fpPairing_bil`: the pairing is multiplication.
* `TauCeti.cupFp_π`: on the classes of two cocycles, the cup square is the class of their cup
  product.
* `TauCeti.cupFp_gradedComm`: the cup square is graded-commutative, `cupFp a b = - cupFp b a`.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter III, §9.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology

universe u

/-! ### The multiplication pairing -/

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- **The multiplication pairing on `𝔽_p`**: multiplication in `ZMod p`, read on the carrier of
`trivialFp p G` through the coordinate `trivialFpEquiv p G`, as a coefficient pairing of the trivial
representation with itself. It is `ZMod p`-bilinear, jointly continuous because the coefficients are
discrete, and equivariant because the action is trivial. -/
noncomputable def fpPairing : TopPairing (trivialFp p G) (trivialFp p G) (trivialFp p G) where
  bil := ((LinearMap.mul (ZMod p) (ZMod p)).compl₁₂ (trivialFpEquiv p G).toLinearMap
    (trivialFpEquiv p G).toLinearMap).compr₂ (trivialFpEquiv p G).symm.toLinearMap
  cont := continuous_of_discreteTopology
  equivariant g x y := by simp only [trivialFp_ρ_apply_apply]

/-- **The pairing is multiplication**: the defining equation of `fpPairing`, through the coordinate
`trivialFpEquiv p G` on the carrier of `trivialFp p G`. -/
theorem fpPairing_bil (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y =
      (trivialFpEquiv p G).symm (trivialFpEquiv p G x * trivialFpEquiv p G y) := by
  unfold fpPairing
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    LinearEquiv.coe_coe]

/-- In the coordinate `trivialFpEquiv p G`, the multiplication pairing is multiplication. -/
@[simp]
theorem trivialFpEquiv_fpPairing_bil (x y : (trivialFp p G).V) :
    trivialFpEquiv p G ((fpPairing p G).bil x y) =
      trivialFpEquiv p G x * trivialFpEquiv p G y := by
  rw [fpPairing_bil, LinearEquiv.apply_symm_apply]

/-- The opposite of the multiplication pairing is itself, because multiplication in `ZMod p` is
commutative. -/
@[simp]
theorem fpPairing_flip : (fpPairing p G).flip = fpPairing p G :=
  TopPairing.ext (LinearMap.ext₂ fun x y ↦ by
    rw [TopPairing.flip_bil, fpPairing_bil, fpPairing_bil, mul_comm])

end Monoid

/-! ### The cup square -/

section Group

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The cup square on `H¹(G, 𝔽_p)`**: the cup product `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)`
at the multiplication pairing, as a `ZMod p`-bilinear map. On the classes of two cocycles it is the
class of their cup product (`cupFp_π`). -/
noncomputable def cupFp : cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 2 :=
  (fpPairing p G).cup 1 1

/-- The cup square is the cup product at the multiplication pairing in bidegree `(1, 1)`. -/
theorem cupFp_def : cupFp p G = (fpPairing p G).cup 1 1 := (rfl)

/-- **The cup square on classes**: the cup square of the classes of two cocycles is the class of
their cup product. -/
@[simp]
theorem cupFp_π (a b : cocycles (trivialFp p G) 1) :
    cupFp p G (π (trivialFp p G) 1 a) (π (trivialFp p G) 1 b) =
      π (trivialFp p G) 2 ((fpPairing p G).cupCocycles 1 1 a b) := by
  rw [cupFp]
  exact (fpPairing p G).cup_π 1 1 a b

/-- **Graded commutativity of the cup square**, `cupFp a b = - cupFp b a`: the bidegree-`(1, 1)`
graded commutativity of the cup product at the multiplication pairing, whose opposite pairing is
itself. -/
theorem cupFp_gradedComm (a b : cohomFp p G 1) : cupFp p G a b = -cupFp p G b a := by
  rw [cupFp, (fpPairing p G).cup_one_one_eq_neg_flip a b, fpPairing_flip]

end Group

end TauCeti
