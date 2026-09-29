/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.Hopfian
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
public import TauCeti.Topology.Compactness.InverseSystem

/-!
# Levelwise comparison along the lower `p`-series

A `PLowerCentralSeriesComparison p G H S` assigns to each datum in `S k` a continuous
surjection `G ⧸ λ_k → H ⧸ λ_k`. Its bonding maps commute with the quotient projections.
When every `S k` is finite and nonempty, there is a compatible sequence of data. If `G` is
compact and `H` is a pro-`p` group, the corresponding quotient maps come from a continuous
surjection `G → H`.

Surjectivity of the bonding maps is unnecessary: a tower of nonempty finite sets already
has a compatible sequence. Surjectivity of the realization maps is essential.

## Main results

* `MonoidHom.pLowerCentralSeriesDesc`: a continuous homomorphism between the quotients by
  `λ_{k+1}` descends to the quotients by `λ_k`, compatibly with the quotient projections; this
  supplies the bonding maps of a comparison whose data are homomorphisms of the finite levels.
* `PLowerCentralSeriesComparison.exists_continuous_surjective`: a compatible sequence of
  finite comparison data is realized at every level by a continuous surjection.
* `PLowerCentralSeriesComparison.exists_continuousMulEquiv`: comparison data in both
  directions give a topological isomorphism realizing the forward data.
* `PLowerCentralSeriesComparison.exists_continuousMulEquiv_preserving`: self-comparison
  data preserving marked elements and all finite character quotients give an automorphism
  preserving the marked elements and the character.

The last result applies to basis changes of a finite-rank free pro-`p` group with a marked
relator. Constructing the finite nonempty sets of admissible basis changes is a separate
hypothesis; the theorem does not construct the corrections used in a normal-form argument.
-/

public section

namespace TauCeti

variable (p : ℕ) (G H : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (S : ℕ → Type*)

section Desc

variable {p G H} [CompactSpace H] {k : ℕ}

/-- **Descent along the lower `p`-series.** A continuous homomorphism between the quotients by
`λ_{k+1}` of two topological groups, the target compact, carries the image of `λ_k` into the image
of `λ_k`, hence descends to a homomorphism between the quotients by `λ_k`. Its defining equation
is `MonoidHom.pLowerCentralSeriesDesc_mk`. -/
noncomputable def _root_.MonoidHom.pLowerCentralSeriesDesc
    (ψ : G ⧸ pLowerCentralSeries p G (k + 1) →* H ⧸ pLowerCentralSeries p H (k + 1))
    (hψ : Continuous ψ) : G ⧸ pLowerCentralSeries p G k →* H ⧸ pLowerCentralSeries p H k :=
  QuotientGroup.lift _ ((QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)).comp
    (ψ.comp (QuotientGroup.mk' _))) (by
      intro g hg
      -- The class of `g ∈ λ_k(G)` lies in `λ_k(G ⧸ λ_{k+1})`, which `ψ` carries into
      -- `λ_k(H ⧸ λ_{k+1})`, the image of `λ_k(H)`.
      have hH : IsClosed ((pLowerCentralSeries p H (k + 1) : Subgroup H) : Set H) :=
        isClosed_pLowerCentralSeries _
      have h1 : ψ (g : G ⧸ pLowerCentralSeries p G (k + 1)) ∈
          pLowerCentralSeries p (H ⧸ pLowerCentralSeries p H (k + 1)) k :=
        ψ.map_pLowerCentralSeries_le hψ k ⟨_, (QuotientGroup.mk' _).map_pLowerCentralSeries_le
          QuotientGroup.continuous_mk k ⟨g, hg, rfl⟩, rfl⟩
      rw [← (QuotientGroup.mk' (pLowerCentralSeries p H (k + 1)))
        |>.map_pLowerCentralSeries_eq_of_surjective QuotientGroup.continuous_mk
          QuotientGroup.continuous_mk.isClosedMap (QuotientGroup.mk'_surjective _)] at h1
      obtain ⟨h, hh, hh'⟩ := h1
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        ← hh', QuotientGroup.mk'_apply, QuotientGroup.mapOfLE_mk, QuotientGroup.eq_one_iff]
      exact hh)

/-- The descended homomorphism on the class of `g` is the class of `ψ ⟦g⟧`. -/
@[simp]
theorem _root_.MonoidHom.pLowerCentralSeriesDesc_mk
    (ψ : G ⧸ pLowerCentralSeries p G (k + 1) →* H ⧸ pLowerCentralSeries p H (k + 1))
    (hψ : Continuous ψ) (g : G) :
    ψ.pLowerCentralSeriesDesc hψ (g : G ⧸ pLowerCentralSeries p G k) =
      QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)
        (ψ (g : G ⧸ pLowerCentralSeries p G (k + 1))) := by
  rw [MonoidHom.pLowerCentralSeriesDesc, QuotientGroup.lift_mk]
  rfl

/-- The descended homomorphism commutes with the quotient projections. -/
theorem _root_.MonoidHom.pLowerCentralSeriesDesc_mapOfLE
    (ψ : G ⧸ pLowerCentralSeries p G (k + 1) →* H ⧸ pLowerCentralSeries p H (k + 1))
    (hψ : Continuous ψ) (x : G ⧸ pLowerCentralSeries p G (k + 1)) :
    ψ.pLowerCentralSeriesDesc hψ (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) x) =
      QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) (ψ x) := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [QuotientGroup.mapOfLE_mk, MonoidHom.pLowerCentralSeriesDesc_mk]

/-- The descent of a surjective homomorphism is surjective. -/
theorem _root_.MonoidHom.pLowerCentralSeriesDesc_surjective
    (ψ : G ⧸ pLowerCentralSeries p G (k + 1) →* H ⧸ pLowerCentralSeries p H (k + 1))
    (hψ : Continuous ψ) (h : Function.Surjective ψ) :
    Function.Surjective (ψ.pLowerCentralSeriesDesc hψ) := by
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mapOfLE_surjective (pLowerCentralSeries_succ_le k) y
  obtain ⟨x, rfl⟩ := h y'
  exact ⟨_, ψ.pLowerCentralSeriesDesc_mapOfLE hψ x⟩

end Desc

/-- Surjective maps between lower `p`-series quotients, indexed by a tower of comparison data.
Applications put their finite-level constraints in `S`; finiteness and nonemptiness are required
only by the realization theorems. -/
structure PLowerCentralSeriesComparison where
  /-- The map realized by one comparison datum. -/
  map : ∀ k, S k → (G ⧸ pLowerCentralSeries p G k) →ₜ*
    (H ⧸ pLowerCentralSeries p H k)
  /-- Every realization covers the target quotient. -/
  map_surjective : ∀ k s, Function.Surjective (map k s)
  /-- Forgetting the last level of comparison data. -/
  bond : ∀ k, S (k + 1) → S k
  /-- Realization commutes with forgetting a level. -/
  commutes : ∀ k s x,
    QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) (map (k + 1) s x) =
      map k (bond k s) (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k) x)

namespace PLowerCentralSeriesComparison

variable {p G H S} [CompactSpace G] [CompactSpace H] [TotallyDisconnectedSpace H]
  [∀ k, Finite (S k)] [∀ k, Nonempty (S k)]

/-- **Levelwise comparison.** Finite nonempty comparison data give a compatible sequence and
a continuous surjection inducing its realization on every quotient. The source need only be
compact and the target any pro-`p` group; neither is assumed finitely generated. -/
theorem exists_continuous_surjective (C : PLowerCentralSeriesComparison p G H S)
    (hH : IsProP p H) (hp : p.Prime) :
    ∃ (s : ∀ k, S k) (φ : G →ₜ* H),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧ Function.Surjective φ ∧
        ∀ k g, (φ g : H ⧸ pLowerCentralSeries p H k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
  obtain ⟨s, hs⟩ := exists_forall_map_succ_eq_of_finite C.bond
  let x (k : ℕ) : G →* H ⧸ pLowerCentralSeries p H k :=
    (C.map k (s k)).toMonoidHom.comp (QuotientGroup.mk' (pLowerCentralSeries p G k))
  have hx : ∀ k, (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)).comp
      (x (k + 1)) = x k := by
    intro k
    ext g
    simpa only [x, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      QuotientGroup.mk'_apply,
      QuotientGroup.mapOfLE_mk, hs k] using
      C.commutes k (s (k + 1)) (g : G ⧸ pLowerCentralSeries p G (k + 1))
  obtain ⟨φ, hφ, _⟩ := hH.existsUnique_monoidHom_mk'_comp_eq_pLowerCentralSeries hp x hx
  have hφk : ∀ k g, (φ g : H ⧸ pLowerCentralSeries p H k) =
      C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) :=
    fun k g ↦ DFunLike.congr_fun (hφ k) g
  have hcont : Continuous φ :=
    (hH.continuous_iff_forall_continuous_mk_pLowerCentralSeries hp).mpr fun k ↦
      ((C.map k (s k)).continuous.comp QuotientGroup.continuous_mk).congr
        fun g ↦ (hφk k g).symm
  have hsurj : Function.Surjective φ := by
    apply surjective_of_forall_surjective_mk'_comp hcont
    intro U
    obtain ⟨k, hk⟩ := hH.exists_pLowerCentralSeries_le hp U
    have hcomp : (QuotientGroup.mk' U.toSubgroup).comp φ =
        (QuotientGroup.mapOfLE hk).comp (x k) := by
      ext g
      simp only [x, MonoidHom.comp_apply, ContinuousMonoidHom.coe_toMonoidHom,
        MonoidHom.coe_ofClass, QuotientGroup.mk'_apply]
      rw [← hφk k g, QuotientGroup.mapOfLE_mk]
    rw [hcomp]
    exact (QuotientGroup.mapOfLE_surjective hk).comp
      ((C.map_surjective k (s k)).comp (QuotientGroup.mk'_surjective _))
  exact ⟨s, ⟨φ, hcont⟩, hs, hsurj, hφk⟩

variable [TotallyDisconnectedSpace G]

/-- **Two-sided comparison.** For a topologically finitely generated pro-`p` source and a pro-`p`
target, comparison data in both directions give an isomorphism realizing a compatible sequence of
the forward data. -/
theorem exists_continuousMulEquiv {T : ℕ → Type*} [∀ k, Finite (T k)] [∀ k, Nonempty (T k)]
    (C : PLowerCentralSeriesComparison p G H S) (D : PLowerCentralSeriesComparison p H G T)
    (hG : IsProP p G) (hGfg : IsTopologicallyFinitelyGenerated G) (hH : IsProP p H)
    (hp : p.Prime) :
    ∃ (s : ∀ k, S k) (e : G ≃ₜ* H),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧
        ∀ k g, (e g : H ⧸ pLowerCentralSeries p H k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
  obtain ⟨s, φ, hs, hφs, hφ⟩ := C.exists_continuous_surjective hH hp
  obtain ⟨_, ψ, _, hψs, _⟩ := D.exists_continuous_surjective hG hp
  have hb := hGfg.bijective_of_surjective_of_surjective φ.continuous hφs ψ.continuous hψs
  let e : G ≃ₜ* H := ContinuousMulEquiv.mk (MulEquiv.ofBijective φ.toMonoidHom hb)
    φ.continuous (φ.continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective φ.toMonoidHom hb).toEquiv))
  exact ⟨s, e, hs, hφ⟩

omit [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- **Comparison preserving relators and characters.** Suppose every level map takes the marked
elements `a` to `b`, and each finite quotient of the character is respected at some level.
Then a self-comparison is realized by an automorphism taking `a` to `b` and intertwining the
characters. The character target may be any profinite group.

The character condition is entirely finite-level: equality of the level-`k` image of `x`
with the class of `y` must imply equality of the prescribed character values modulo `U`.
The level `k` may depend on `U`. -/
theorem exists_continuousMulEquiv_preserving {ι K : Type*}
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [TotallyDisconnectedSpace K] (C : PLowerCentralSeriesComparison p G G S)
    (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime)
    (a b : ι → G) (χ ψ : G →ₜ* K)
    (hmark : ∀ k s i, C.map k s (a i : G ⧸ pLowerCentralSeries p G k) =
      (b i : G ⧸ pLowerCentralSeries p G k))
    (hchar : ∀ U : OpenNormalSubgroup K, ∃ k, ∀ (s : S k) (x y : G),
      C.map k s (x : G ⧸ pLowerCentralSeries p G k) =
          (y : G ⧸ pLowerCentralSeries p G k) →
        (ψ y : K ⧸ U.toSubgroup) = (χ x : K ⧸ U.toSubgroup)) :
    ∃ (s : ∀ k, S k) (e : G ≃ₜ* G),
      (∀ k, C.bond k (s (k + 1)) = s k) ∧
        (∀ k g, (e g : G ⧸ pLowerCentralSeries p G k) =
          C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k)) ∧
        (∀ i, e (a i) = b i) ∧ ψ.comp (e : G →ₜ* G) = χ := by
  obtain ⟨s, φ, hs, hφs, hφ⟩ := C.exists_continuous_surjective hG hp
  let e := hfg.continuousMulEquivOfSurjective φ.continuous hφs
  have he (g : G) : e g = φ g :=
    hfg.continuousMulEquivOfSurjective_apply φ.continuous hφs g
  have hlevel : ∀ k g, (e g : G ⧸ pLowerCentralSeries p G k) =
      C.map k (s k) (g : G ⧸ pLowerCentralSeries p G k) := by
    intro k g
    rw [he]
    exact hφ k g
  refine ⟨s, e, hs, hlevel, ?_, ?_⟩
  · intro i
    exact eq_of_forall_mk_eq_of_iInf_eq_bot (hG.iInf_pLowerCentralSeries_eq_bot hp)
      fun k ↦ (hlevel k (a i)).trans (hmark k (s k) i)
  · ext g
    apply eq_of_forall_mk_eq_of_iInf_eq_bot (Subgroup.iInf_openNormalSubgroup_eq_bot (G := K))
    intro U
    obtain ⟨k, hk⟩ := hchar U
    exact hk (s k) g (e g) (hlevel k g).symm

end PLowerCentralSeriesComparison

end TauCeti
