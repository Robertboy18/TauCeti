/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basis
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic
import TauCeti.NumberTheory.Padics.InverseLimit

/-!
# The prescription property as prescribed values of crossed homomorphisms

Let `G` be a pro-`p` group, `χ : G →ₜ* ℤ_pˣ` a continuous character and `I(χ)/pⁱ = ZModTwist χ i`
the twisted coefficients `ℤ/pⁱ` with `g` acting by `χ(g)`. Labute's prescription property of `χ`
(`TauCeti.HasPrescriptionProperty`) asks that every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` be
surjective. This file proves its third formulation (Labute, Prop. 6, condition (iii)): for a
topologically finitely generated pro-`p` group and a minimal generating tuple `g₁, …, gₙ`, the
property holds exactly when every tuple `c₁, …, cₙ` of `p`-adic integers is the tuple of values of
a compatible system of continuous crossed homomorphisms `fᵢ : G → I(χ)/pⁱ`, `fᵢ(gⱼ) = cⱼ mod pⁱ`.
Such a compatible system is the same thing as a continuous crossed homomorphism `F : G → ℤ_p`,
`F(xy) = χ(x) F(y) + F(x)`, with values `F(gⱼ) = cⱼ`, since `ℤ_p` is the inverse limit of the
`ℤ/pⁱ`; both forms are proved, and the second is the one downstream applications read: it converts
Kummer-compatible finite-level data into prescribed values of the canonical character.

Two facts about the bottom level `I(χ)/p` drive the proofs. A pro-`p` group acts trivially on it,
because a continuous character of a pro-`p` group takes values in the principal units `1 + pℤ_p`
(`TauCeti.IsProP.charScalar_one_eq_one`); hence the continuous `1`-cocycles with values in `I(χ)/p`
are the continuous homomorphisms `G → 𝔽_p`, which are determined by their values on a topological
generating set and take any prescribed values on a family that is linearly independent in the
Frattini quotient (`TauCeti.IsTopologicallyFinitelyGenerated.exists_continuousMonoidHom_apply_eq`).
Going up one level, the prescription property lifts a cocycle from `I(χ)/pⁱ` to `I(χ)/pⁱ⁺¹` up to a
coboundary, which is removed by lifting its potential; the values on the generators are then
corrected by a homomorphism into `pⁱ I(χ)/pⁱ⁺¹ ≅ 𝔽_p`, on which `G` acts trivially.

## Main results

* `TauCeti.IsProP.charScalar_one_eq_one`: a pro-`p` group acts trivially on `I(χ)/p`.
* `TauCeti.HasPrescriptionProperty.exists_forall_reduce_eq`: under the prescription property a
  continuous `1`-cocycle with values in `I(χ)/pʲ` is the pointwise reduction of one with values in
  `I(χ)/pⁿ`, for `j ≤ n`.
* `TauCeti.HasPrescriptionProperty.exists_forall_reduce_eq_and_val_eq`: under the prescription
  property, every tuple `c : ι → ℤ_p` is realized on a family `g` with linearly independent
  Frattini classes by a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`.
* `TauCeti.hasPrescriptionProperty_of_forall_exists_forall_reduce_eq`: conversely, if every tuple is
  so realized on a topological generating family, the character has the prescription property.
* `TauCeti.IsProP.hasPrescriptionProperty_iff_forall_exists_forall_reduce_eq`: the equivalence, for
  the lifts of a basis of the Frattini quotient, that is for a minimal generating tuple.
* `TauCeti.exists_continuous_forall_toZModPow_eq_val`: a compatible system of continuous
  `1`-cocycles with values in the `I(χ)/pⁱ` is the family of reductions of a continuous crossed
  homomorphism `G → ℤ_p`.
* `TauCeti.IsProP.hasPrescriptionProperty_iff_forall_exists_continuous_forall_mul_eq`: the
  prescription property is the existence, for every tuple `c`, of a continuous crossed
  homomorphism `F : G → ℤ_p` for `χ` with `F(gⱼ) = cⱼ` on a minimal generating tuple.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The bottom level of the twisted coefficients of a pro-`p` group -/

section LevelOne

variable (hG : IsProP p G) (χ : G →ₜ* ℤ_[p]ˣ)
include hG

/-- A continuous character of a pro-`p` group takes values in the principal units `1 + pℤ_p`: its
range is a pro-`p` subgroup of `ℤ_pˣ`. -/
theorem IsProP.mem_unitsPrincipal_one (g : G) : χ g ∈ unitsPrincipal p 1 :=
  have : IsProP p χ.toMonoidHom.range :=
    hG.of_surjective χ.toMonoidHom.rangeRestrict (continuous_induced_rng.mpr χ.continuous)
      χ.toMonoidHom.rangeRestrict_surjective
  this.le_unitsPrincipal_one ⟨g, rfl⟩

/-- **A pro-`p` group acts trivially on `I(χ)/p`**: the scalar `χ g mod p` is `1`. -/
theorem IsProP.charScalar_one_eq_one (g : G) : charScalar χ 1 g = 1 := by
  rw [charScalar_apply]
  exact mem_unitsPrincipal_iff_toZModPow.mp (hG.mem_unitsPrincipal_one χ g)

/-- The action of a pro-`p` group on the bottom level `I(χ)/p` of the twisted coefficients is
trivial. -/
theorem IsProP.smul_zModTwist_one_eq_self (g : G) (x : ZModTwist χ 1) : g • x = x :=
  ZModTwist.ext (by rw [ZModTwist.val_smul, hG.charScalar_one_eq_one χ g, one_mul])

end LevelOne

/-! ### Exact lifting of cocycles between levels -/

section Lift

variable {χ : G →ₜ* ℤ_[p]ˣ} (hχ : HasPrescriptionProperty χ)
include hχ

/-- **Cocycles lift exactly under the prescription property.** A continuous `1`-cocycle
`f : G → I(χ)/pʲ` is the pointwise reduction of a continuous `1`-cocycle `G → I(χ)/pⁿ`, `j ≤ n`, not
only up to a coboundary: the coboundary by which a lift of the class of `f` misses `f` is removed by
lifting its potential. -/
theorem HasPrescriptionProperty.exists_forall_reduce_eq {j n : ℕ} (h : j ≤ n)
    (f : Z1 G (ZModTwist χ j)) :
    ∃ f' : Z1 G (ZModTwist χ n),
      ∀ x, ZModTwist.reduce χ h ((f' : G → ZModTwist χ n) x) = (f : G → ZModTwist χ j) x := by
  obtain ⟨y, hy⟩ := hχ.surjective_explicitCoeff1_reduce h (f : H1 G (ZModTwist χ j))
  induction y using QuotientAddGroup.induction_on with
  | _ f₁ =>
  rw [explicitCoeff1_mk, H1pi_eq_iff, mem_B1_iff] at hy
  obtain ⟨m, hm⟩ := hy
  obtain ⟨m', rfl⟩ := ZModTwist.reduce_surjective χ h m
  refine ⟨f₁ - ⟨d0 G (ZModTwist χ n) m', B1_le_Z1 G _ (d0_mem_B1 m')⟩, fun x ↦ ?_⟩
  -- `cocyclesMap1_apply` is used as a term: its continuity argument is stated for the coerced
  -- additive homomorphism, which `rw` cannot match against the bundled equivariant one.
  have hx : x • ZModTwist.reduce χ h m' - ZModTwist.reduce χ h m' =
      ZModTwist.reduce χ h ((f₁ : G → ZModTwist χ n) x) - (f : G → ZModTwist χ j) x :=
    (hm x).trans (congrArg (· - (f : G → ZModTwist χ j) x)
      (cocyclesMap1_apply G _ G _ (ContinuousMonoidHom.id G) _ continuous_of_discreteTopology
        (fun g m ↦ (ZModTwist.reduce χ h).map_smul g m) f₁ x))
  have hd : ((⟨d0 G (ZModTwist χ n) m', B1_le_Z1 G _ (d0_mem_B1 m')⟩ :
      Z1 G (ZModTwist χ n)) : G → ZModTwist χ n) = d0 G (ZModTwist χ n) m' :=
    rfl
  rw [AddSubgroup.coe_sub, Pi.sub_apply, hd, d0_apply, map_sub, map_sub, map_smul, hx,
    sub_sub_cancel]

end Lift

/-! ### Compatible systems with prescribed values -/

section System

variable [IsTopologicalGroup G] [CompactSpace G] {χ : G →ₜ* ℤ_[p]ˣ}

variable (hχ : HasPrescriptionProperty χ) (hG : IsProP p G)
  (hfg : IsTopologicallyFinitelyGenerated G) {ι : Type*} {g : ι → G}
  (hg : LinearIndependent (ZMod p) fun k ↦
    Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)))
  (c : ι → ℤ_[p])
include hχ hG hfg hg

/-- **One step of the compatible system.** Under the prescription property, a continuous
`1`-cocycle `f : G → I(χ)/pⁱ` with values `c k mod pⁱ` on a family `g` with linearly independent
Frattini classes is the reduction of a continuous `1`-cocycle `G → I(χ)/pⁱ⁺¹` with values
`c k mod pⁱ⁺¹`. -/
theorem HasPrescriptionProperty.exists_succ_forall_reduce_eq_and_val_eq {i : ℕ}
    (f : Z1 G (ZModTwist χ i))
    (hf : ∀ k, ((f : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)) :
    ∃ f' : Z1 G (ZModTwist χ (i + 1)),
      (∀ x, ZModTwist.reduce χ (Nat.le_succ i) ((f' : G → ZModTwist χ (i + 1)) x) =
        (f : G → ZModTwist χ i) x) ∧
      ∀ k, ((f' : G → ZModTwist χ (i + 1)) (g k)).val = PadicInt.toZModPow (i + 1) (c k) := by
  obtain ⟨f₀, hf₀⟩ := hχ.exists_forall_reduce_eq (Nat.le_succ i) f
  -- the values on the generators are corrected by `pⁱ` times a homomorphism into `I(χ)/p`
  have h1 : 1 + i = i + 1 := Nat.add_comm 1 i
  have hδ (k : ι) : ∃ ε : ZModTwist χ 1, ZModTwist.mulPow χ h1 ε =
      ⟨PadicInt.toZModPow (i + 1) (c k)⟩ - (f₀ : G → ZModTwist χ (i + 1)) (g k) := by
    obtain ⟨ε, hε⟩ := (ZModTwist.shortExact χ h1).exists_incl_eq
      (b := ⟨PadicInt.toZModPow (i + 1) (c k)⟩ - (f₀ : G → ZModTwist χ (i + 1)) (g k)) (by
        rw [ZModTwist.shortExact_proj_apply, map_sub, hf₀, ZModTwist.ext_iff, ZModTwist.val_sub,
          ZModTwist.val_reduce, ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ (Nat.le_succ i),
          hf, sub_self, ZModTwist.val_zero])
    rw [ZModTwist.shortExact_incl_apply] at hε
    exact ⟨ε, hε⟩
  choose ε hε using hδ
  -- `I(χ)/p` is an `𝔽_p`-vector space, so a continuous `𝔽_p`-character takes the values `ε`
  let : Module (ZMod p) (ZModTwist χ 1) := AddCommGroup.zmodModule fun x ↦
    (ZModTwist.equiv χ 1).injective (by
      rw [map_nsmul, map_zero, ZModTwist.equiv_apply, nsmul_eq_mul,
        (CharP.cast_eq_zero_iff (ZMod (p ^ 1)) (p ^ 1) p).mpr (by rw [pow_one]), zero_mul])
  obtain ⟨ψ, hψ⟩ := hfg.exists_continuousMonoidHom_apply_eq hg ε
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : Z1 G (ZModTwist χ 1),
      ∀ x, (h₁ : G → ZModTwist χ 1) x = Multiplicative.toAdd (ψ x) :=
    ⟨(Z1EquivOfSmulEqSelf (hG.smul_zModTwist_one_eq_self χ)).symm (Additive.ofMul ψ), fun x ↦ by
      rw [Z1EquivOfSmulEqSelf_symm_apply, toMul_ofMul]⟩
  obtain ⟨h', hh'⟩ : ∃ h' : Z1 G (ZModTwist χ (i + 1)), ∀ x,
      (h' : G → ZModTwist χ (i + 1)) x = ZModTwist.mulPow χ h1 ((h₁ : G → ZModTwist χ 1) x) :=
    ⟨cocyclesMap1 G (ZModTwist χ 1) G (ZModTwist χ (i + 1)) (ContinuousMonoidHom.id G)
      (ZModTwist.mulPow χ h1) continuous_of_discreteTopology
      (fun g m ↦ (ZModTwist.mulPow χ h1).map_smul g m) h₁,
      fun x ↦ cocyclesMap1_apply G _ G _ (ContinuousMonoidHom.id G) _
        continuous_of_discreteTopology (fun g m ↦ (ZModTwist.mulPow χ h1).map_smul g m) h₁ x⟩
  refine ⟨f₀ + h', fun x ↦ ?_, fun k ↦ ?_⟩
  · rw [AddSubgroup.coe_add, Pi.add_apply, map_add, hf₀, hh', ZModTwist.reduce_mulPow, add_zero]
  · rw [AddSubgroup.coe_add, Pi.add_apply, hh', hh₁, hψ, toAdd_ofAdd, hε, add_sub_cancel]

/-- **The prescription property gives compatible systems of crossed homomorphisms with
prescribed values** (Labute, Prop. 6, (i) ⇒ (iii)). Let `G` be a topologically finitely generated
pro-`p` group, `χ` a continuous character with the prescription property and `g : ι → G` a family
whose classes in the Frattini quotient are linearly independent over `𝔽_p`. Then for every
`c : ι → ℤ_p` there are continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`, compatible under the reductions
`I(χ)/pⁱ → I(χ)/pʲ`, with `fᵢ (g k) = c k mod pⁱ` for every `i` and `k`. -/
theorem HasPrescriptionProperty.exists_forall_reduce_eq_and_val_eq :
    ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k) := by
  -- the admissible cocycles at each level, and the step between consecutive levels
  let S : ℕ → Type u := fun i ↦
    {f : Z1 G (ZModTwist χ i) //
      ∀ k, ((f : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)}
  have hstep : ∀ (i : ℕ) (f : S i), ∃ f' : S (i + 1), ∀ x,
      ZModTwist.reduce χ (Nat.le_succ i) ((f'.1 : G → ZModTwist χ (i + 1)) x) =
        (f.1 : G → ZModTwist χ i) x := fun i f ↦ by
    obtain ⟨f', hf'₁, hf'₂⟩ := hχ.exists_succ_forall_reduce_eq_and_val_eq hG hfg hg c f.1 f.2
    exact ⟨⟨f', hf'₂⟩, hf'₁⟩
  choose step hstep using hstep
  have h0 : S 0 := ⟨0, fun k ↦
    have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
    Subsingleton.elim _ _⟩
  let seq : ∀ i, S i := fun i ↦ Nat.rec h0 step i
  refine ⟨fun i ↦ (seq i).1, fun i j h x ↦ ?_, fun i k ↦ (seq i).2 k⟩
  induction i, h using Nat.le_induction with
  | base => exact ZModTwist.reduce_self χ _
  | succ i hji ih =>
    calc ZModTwist.reduce χ (hji.trans (Nat.le_succ i))
          (((seq (i + 1)).1 : G → ZModTwist χ (i + 1)) x)
        = ZModTwist.reduce χ hji (ZModTwist.reduce χ (Nat.le_succ i)
            (((seq (i + 1)).1 : G → ZModTwist χ (i + 1)) x)) :=
          (ZModTwist.reduce_reduce χ (Nat.le_succ i) hji _).symm
      _ = ((seq j).1 : G → ZModTwist χ j) x := by rw [hstep i (seq i) x, ih]

end System

/-! ### Prescribed values give the prescription property -/

section Converse

variable [IsTopologicalGroup G] {χ : G →ₜ* ℤ_[p]ˣ} {ι : Type*} {g : ι → G}
  (hg : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
include hg

/-- **Compatible systems with prescribed values give the prescription property** (Labute,
Prop. 6, (iii) ⇒ (i)). If `g` generates `G` topologically and every `c : ι → ℤ_p` is the tuple of
values on `g` of a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`, then `χ` has the
prescription property: a continuous `1`-cocycle with values in `I(χ)/p` is determined by its values
on `g`, so it is the bottom member of such a system, and the members above reduce onto it. -/
theorem hasPrescriptionProperty_of_forall_exists_forall_reduce_eq
    (h : ∀ c : ι → ℤ_[p], ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)) :
    HasPrescriptionProperty χ := by
  refine (hasPrescriptionProperty_iff χ).2 fun i hi y ↦ ?_
  induction y using QuotientAddGroup.induction_on with
  | _ f₁ =>
  choose c hc using fun k ↦
    ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) 1) ((f₁ : G → ZModTwist χ 1) (g k)).val
  obtain ⟨f, hf, hfc⟩ := h c
  have h1 : (f 1 : G → ZModTwist χ 1) = f₁ :=
    eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top (f 1).2 f₁.2 hg (by
      rintro _ ⟨k, rfl⟩
      exact ZModTwist.ext ((hfc 1 k).trans (hc k)))
  refine ⟨f i, ?_⟩
  rw [explicitCoeff1_mk]
  refine congrArg _ (Subtype.ext (funext fun x ↦ ?_))
  rw [← congrFun h1 x, ← hf hi x]
  exact cocyclesMap1_apply G _ G _ (ContinuousMonoidHom.id G) _ continuous_of_discreteTopology
    (fun g m ↦ (ZModTwist.reduce χ hi).map_smul g m) (f i) x

end Converse

/-- **Labute's third formulation of the prescription property** (Labute, Prop. 6, (i) ⇔ (iii)).
Let `G` be a topologically finitely generated pro-`p` group and `g : ι → G` a minimal generating
tuple, that is a family of lifts of a basis `b` of the Frattini quotient over `𝔽_p`. A continuous
character `χ` has the prescription property exactly when every `c : ι → ℤ_p` is the tuple of values
on `g` of a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`. -/
theorem IsProP.hasPrescriptionProperty_iff_forall_exists_forall_reduce_eq [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G))) {g : ι → G}
    (hgb : ∀ k, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)) = b k)
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ c : ι → ℤ_[p], ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k) :=
  ⟨fun hχ c ↦ hχ.exists_forall_reduce_eq_and_val_eq hG hfg
    (by rw [show (fun k ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k))) = b from
      funext hgb]; exact b.linearIndependent) c,
    hasPrescriptionProperty_of_forall_exists_forall_reduce_eq
      (topologicallyGenerates_of_basis_frattiniQuotient hG b g hgb)⟩

/-! ### Crossed homomorphisms with values in `ℤ_p`

A compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ` is the family of reductions of a
single continuous map `F : G → ℤ_p` satisfying the crossed-homomorphism identity
`F (x * y) = χ x * F y + F x` for the action of `G` on `ℤ_p` through `χ`, and conversely. The
identity is written out rather than expressed through a module structure on `ℤ_p`, which would
install a second action on a Mathlib type. -/

section PadicInt

variable {χ : G →ₜ* ℤ_[p]ˣ}

/-- **A compatible system of crossed homomorphisms assembles into a `p`-adic one.** Continuous
`1`-cocycles `fᵢ : G → I(χ)/pⁱ` compatible under the reductions are the reductions modulo `pⁱ` of a
continuous map `F : G → ℤ_p` with `F (x * y) = χ x * F y + F x`. -/
theorem exists_continuous_forall_toZModPow_eq_val (f : ∀ i : ℕ, Z1 G (ZModTwist χ i))
    (hf : ∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
      ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) :
    ∃ F : G → ℤ_[p], Continuous F ∧ (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧
      ∀ (i : ℕ) (x : G), PadicInt.toZModPow i (F x) = ((f i : G → ZModTwist χ i) x).val := by
  -- the residue family of `x`
  let r : G → PadicInt.inverseLimit p := fun x ↦
    ⟨fun i ↦ ((f i : G → ZModTwist χ i) x).val, PadicInt.mem_inverseLimit_iff.mpr fun m n hmn ↦ by
      have h := congrArg ZModTwist.val (hf hmn x)
      rwa [ZModTwist.val_reduce, ZMod.castHom_apply] at h⟩
  have hr (i : ℕ) (x : G) :
      PadicInt.toZModPow i (PadicInt.fromInverseLimit p (r x)) =
        ((f i : G → ZModTwist χ i) x).val := by
    have h := RingHom.congr_fun (PadicInt.toZModPow_fromInverseLimit p i) (r x)
    rwa [RingHom.comp_apply, PadicInt.inverseLimit.proj_apply] at h
  refine ⟨fun x ↦ PadicInt.fromInverseLimit p (r x), ?_, fun x y ↦ ?_, hr⟩
  · refine (PadicInt.continuous_fromInverseLimit p).comp (Continuous.subtype_mk ?_ _)
    exact continuous_pi fun i ↦
      continuous_of_discreteTopology.comp (mem_Z1_iff.1 (f i).2).1
  · refine PadicInt.ext_of_toZModPow.1 fun i ↦ ?_
    have h := congrArg ZModTwist.val ((mem_Z1_iff.1 (f i).2).2 x y)
    rw [ZModTwist.val_add, ZModTwist.val_smul, charScalar_apply] at h
    rw [map_add, map_mul, hr, hr, hr, h]

variable [IsTopologicalGroup G] [CompactSpace G] {ι : Type*} {g : ι → G}

/-- **The prescription property gives `p`-adic crossed homomorphisms with prescribed values.**
Let `G` be a topologically finitely generated pro-`p` group, `χ` a continuous character with the
prescription property and `g : ι → G` a family whose classes in the Frattini quotient are linearly
independent over `𝔽_p`. Then for every `c : ι → ℤ_p` there is a continuous `F : G → ℤ_p` with
`F (x * y) = χ x * F y + F x` and `F (g k) = c k`. -/
theorem HasPrescriptionProperty.exists_continuous_forall_mul_eq_and_apply_eq
    (hχ : HasPrescriptionProperty χ) (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
    (hg : LinearIndependent (ZMod p) fun k ↦
      Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)))
    (c : ι → ℤ_[p]) :
    ∃ F : G → ℤ_[p], Continuous F ∧ (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧
      ∀ k, F (g k) = c k := by
  obtain ⟨f, hf, hfc⟩ := hχ.exists_forall_reduce_eq_and_val_eq hG hfg hg c
  obtain ⟨F, hFc, hFmul, hF⟩ := exists_continuous_forall_toZModPow_eq_val f hf
  exact ⟨F, hFc, hFmul, fun k ↦ PadicInt.ext_of_toZModPow.1 fun i ↦ (hF i (g k)).trans (hfc i k)⟩

omit [CompactSpace G] in
/-- **`p`-adic crossed homomorphisms with prescribed values give the prescription property.** If `g`
generates `G` topologically and every `c : ι → ℤ_p` is the tuple of values on `g` of a continuous
`F : G → ℤ_p` with `F (x * y) = χ x * F y + F x`, then `χ` has the prescription property: the
reductions of `F` modulo the `pⁱ` form a compatible system of continuous `1`-cocycles. -/
theorem hasPrescriptionProperty_of_forall_exists_continuous_forall_mul_eq
    (hg : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
    (h : ∀ c : ι → ℤ_[p], ∃ F : G → ℤ_[p], Continuous F ∧
      (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧ ∀ k, F (g k) = c k) :
    HasPrescriptionProperty χ := by
  refine hasPrescriptionProperty_of_forall_exists_forall_reduce_eq hg fun c ↦ ?_
  obtain ⟨F, hFc, hFmul, hF⟩ := h c
  refine ⟨fun i ↦ ⟨fun x ↦ ⟨PadicInt.toZModPow i (F x)⟩, mem_Z1_iff.2 ⟨?_, fun x y ↦ ?_⟩⟩,
    fun i j hji x ↦ ?_, fun i k ↦ ?_⟩
  · exact (continuous_of_discreteTopology (f := fun t : ZMod (p ^ i) ↦
      (⟨t⟩ : ZModTwist χ i))).comp ((PadicInt.continuous_toZModPow i).comp hFc)
  · exact ZModTwist.ext (by
      simp only [ZModTwist.val_add, ZModTwist.val_smul, charScalar_apply, hFmul, map_add, map_mul])
  · exact ZModTwist.ext (by
      simp only [ZModTwist.val_reduce, ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ hji])
  · exact congrArg (PadicInt.toZModPow i) (hF k)

/-- **Labute's third formulation of the prescription property, `p`-adic form** (Labute, Prop. 6,
(i) ⇔ (iii)). Let `G` be a topologically finitely generated pro-`p` group and `g : ι → G` a minimal
generating tuple, that is a family of lifts of a basis `b` of the Frattini quotient over `𝔽_p`. A
continuous character `χ` has the prescription property exactly when every `c : ι → ℤ_p` is the tuple
of values on `g` of a continuous crossed homomorphism `F : G → ℤ_p` for `χ`, that is a continuous
`F` with `F (x * y) = χ x * F y + F x`. -/
theorem IsProP.hasPrescriptionProperty_iff_forall_exists_continuous_forall_mul_eq
    [TotallyDisconnectedSpace G] (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    (hgb : ∀ k, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)) = b k)
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ c : ι → ℤ_[p], ∃ F : G → ℤ_[p], Continuous F ∧
      (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧ ∀ k, F (g k) = c k :=
  ⟨fun hχ c ↦ hχ.exists_continuous_forall_mul_eq_and_apply_eq hG hfg
    (by rw [show (fun k ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k))) = b from
      funext hgb]; exact b.linearIndependent) c,
    hasPrescriptionProperty_of_forall_exists_continuous_forall_mul_eq
      (topologicallyGenerates_of_basis_frattiniQuotient hG b g hgb)⟩

end PadicInt

end TauCeti
