/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00

/-!
# M11 coset deductions: transition group 02

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible016 : deductions016.all eligible = true := by
  simp only [deductions016, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_016 :
    deductions016.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits016 =
      bits017 := by
  decide +kernel

theorem eligible017 : deductions017.all eligible = true := by
  simp only [deductions017, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_017 :
    deductions017.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits017 =
      bits018 := by
  decide +kernel

theorem eligible018 : deductions018.all eligible = true := by
  simp only [deductions018, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_018 :
    deductions018.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits018 =
      bits019 := by
  decide +kernel

theorem eligible019 : deductions019.all eligible = true := by
  simp only [deductions019, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_019 :
    deductions019.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits019 =
      bits020 := by
  decide +kernel

theorem eligible020 : deductions020.all eligible = true := by
  simp only [deductions020, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_020 :
    deductions020.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits020 =
      bits021 := by
  decide +kernel

theorem eligible021 : deductions021.all eligible = true := by
  simp only [deductions021, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_021 :
    deductions021.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits021 =
      bits022 := by
  decide +kernel

theorem eligible022 : deductions022.all eligible = true := by
  simp only [deductions022, List.all_cons, List.all_nil, eligible, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_022 :
    deductions022.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits022 =
      bits023 := by
  decide +kernel

theorem eligible023 : deductions023.all eligible = true := by
  simp only [deductions023, List.all_cons, List.all_nil, eligible, r2_mem, r3_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_023 :
    deductions023.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits023 =
      bits024 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
