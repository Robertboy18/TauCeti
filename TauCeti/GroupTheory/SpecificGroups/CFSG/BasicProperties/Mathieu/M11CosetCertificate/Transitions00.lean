/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00

/-!
# M11 coset deductions: transition group 00

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible000 : deductions000.all eligible = true := by
  simp only [deductions000, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_000 :
    deductions000.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits000 =
      bits001 := by
  decide +kernel

theorem eligible001 : deductions001.all eligible = true := by
  simp only [deductions001, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_001 :
    deductions001.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits001 =
      bits002 := by
  decide +kernel

theorem eligible002 : deductions002.all eligible = true := by
  simp only [deductions002, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_002 :
    deductions002.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits002 =
      bits003 := by
  decide +kernel

theorem eligible003 : deductions003.all eligible = true := by
  simp only [deductions003, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_003 :
    deductions003.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits003 =
      bits004 := by
  decide +kernel

theorem eligible004 : deductions004.all eligible = true := by
  simp only [deductions004, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_004 :
    deductions004.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits004 =
      bits005 := by
  decide +kernel

theorem eligible005 : deductions005.all eligible = true := by
  simp only [deductions005, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_005 :
    deductions005.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits005 =
      bits006 := by
  decide +kernel

theorem eligible006 : deductions006.all eligible = true := by
  simp only [deductions006, List.all_cons, List.all_nil, eligible, r0_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_006 :
    deductions006.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits006 =
      bits007 := by
  decide +kernel

theorem eligible007 : deductions007.all eligible = true := by
  simp only [deductions007, List.all_cons, List.all_nil, eligible, r0_mem, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_007 :
    deductions007.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits007 =
      bits008 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
