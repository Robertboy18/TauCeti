/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership07

/-!
# M11 coset deductions: transition group 09

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible072 : deductions072.all eligible = true := by
  simp only [deductions072, List.all_cons, List.all_nil, eligible, r488_mem, r489_mem, r490_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_072 :
    deductions072.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits072 =
      bits073 := by
  decide +kernel

theorem eligible073 : deductions073.all eligible = true := by
  simp only [deductions073, List.all_cons, List.all_nil, eligible, r490_mem, r491_mem, r492_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_073 :
    deductions073.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits073 =
      bits074 := by
  decide +kernel

theorem eligible074 : deductions074.all eligible = true := by
  simp only [deductions074, List.all_cons, List.all_nil, eligible, r492_mem, r493_mem, r494_mem,
    r495_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_074 :
    deductions074.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits074 =
      bits075 := by
  decide +kernel

theorem eligible075 : deductions075.all eligible = true := by
  simp only [deductions075, List.all_cons, List.all_nil, eligible, r495_mem, r496_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_075 :
    deductions075.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits075 =
      bits076 := by
  decide +kernel

theorem eligible076 : deductions076.all eligible = true := by
  simp only [deductions076, List.all_cons, List.all_nil, eligible, r496_mem, r497_mem, r498_mem,
    r499_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_076 :
    deductions076.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits076 =
      bits077 := by
  decide +kernel

theorem eligible077 : deductions077.all eligible = true := by
  simp only [deductions077, List.all_cons, List.all_nil, eligible, r499_mem, r500_mem, r501_mem,
    r502_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_077 :
    deductions077.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits077 =
      bits078 := by
  decide +kernel

theorem eligible078 : deductions078.all eligible = true := by
  simp only [deductions078, List.all_cons, List.all_nil, eligible, r502_mem, r503_mem, r504_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_078 :
    deductions078.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits078 =
      bits079 := by
  decide +kernel

theorem eligible079 : deductions079.all eligible = true := by
  simp only [deductions079, List.all_cons, List.all_nil, eligible, r504_mem, r505_mem, r506_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_079 :
    deductions079.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits079 =
      bits080 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
