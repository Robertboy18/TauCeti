/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership01
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership02
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership03
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership05
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership08
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership09

/-!
# M11 coset deductions: transition group 04

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible032 : deductions032.all eligible = true := by
  simp only [deductions032, List.all_cons, List.all_nil, eligible, r11_mem, r12_mem, r13_mem,
    r14_mem, r15_mem, r16_mem, r17_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_032 :
    deductions032.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits032 =
      bits033 := by
  decide +kernel

theorem eligible033 : deductions033.all eligible = true := by
  simp only [deductions033, List.all_cons, List.all_nil, eligible, r17_mem, r18_mem, r19_mem,
    r20_mem, r21_mem, r22_mem, r24_mem, r26_mem, r27_mem, r28_mem, r30_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_033 :
    deductions033.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits033 =
      bits034 := by
  decide +kernel

theorem eligible034 : deductions034.all eligible = true := by
  simp only [deductions034, List.all_cons, List.all_nil, eligible, r31_mem, r32_mem, r33_mem,
    r34_mem, r35_mem, r37_mem, r39_mem, r40_mem, r41_mem, r46_mem, r47_mem, r54_mem, r55_mem,
    r56_mem, r59_mem, r60_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_034 :
    deductions034.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits034 =
      bits035 := by
  decide +kernel

theorem eligible035 : deductions035.all eligible = true := by
  simp only [deductions035, List.all_cons, List.all_nil, eligible, r61_mem, r62_mem, r64_mem,
    r65_mem, r66_mem, r77_mem, r88_mem, r89_mem, r90_mem, r91_mem, r96_mem, r97_mem, r111_mem,
    r113_mem, r121_mem, r140_mem, r142_mem, r143_mem, r145_mem, r164_mem, r171_mem, r175_mem,
    r202_mem, r239_mem, r240_mem, r322_mem, r336_mem, r543_mem, decide_true, Bool.true_or,
    Bool.true_and]

theorem transition_035 :
    deductions035.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits035 =
      bits036 := by
  decide +kernel

theorem eligible036 : deductions036.all eligible = true := by
  simp only [deductions036, List.all_cons, List.all_nil, eligible, r544_mem, r545_mem, r546_mem,
    r547_mem, r548_mem, r549_mem, r550_mem, r551_mem, r552_mem, r553_mem, r554_mem, r555_mem,
    r556_mem, r557_mem, r558_mem, r559_mem, r560_mem, r561_mem, r562_mem, r563_mem, r564_mem,
    r565_mem, r566_mem, r567_mem, r568_mem, r569_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_036 :
    deductions036.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits036 =
      bits037 := by
  decide +kernel

theorem eligible037 : deductions037.all eligible = true := by
  simp only [deductions037, List.all_cons, List.all_nil, eligible, r570_mem, r571_mem, r572_mem,
    r573_mem, r574_mem, r575_mem, r576_mem, r577_mem, r578_mem, r579_mem, r580_mem, r581_mem,
    r582_mem, r583_mem, r584_mem, r585_mem, r586_mem, r587_mem, r588_mem, r589_mem, r590_mem,
    r591_mem, r592_mem, r593_mem, r594_mem, r595_mem, r596_mem, r597_mem, r598_mem, r599_mem,
    r600_mem, r601_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_037 :
    deductions037.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits037 =
      bits038 := by
  decide +kernel

theorem eligible038 : deductions038.all eligible = true := by
  simp only [deductions038, List.all_cons, List.all_nil, eligible, r1_mem, r602_mem, r603_mem,
    r604_mem, r605_mem, r606_mem, r607_mem, r608_mem, r609_mem, r610_mem, r611_mem, r612_mem,
    r613_mem, r614_mem, r615_mem, r616_mem, r617_mem, r618_mem, r619_mem, r620_mem, r621_mem,
    r622_mem, r623_mem, r624_mem, r625_mem, r626_mem, r627_mem, r628_mem, r629_mem, r630_mem,
    r631_mem, decide_true, Bool.true_or, Bool.true_and, root_word, subgroupWords, List.mem_cons,
    true_or, or_true, Bool.or_true]

theorem transition_038 :
    deductions038.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits038 =
      bits039 := by
  decide +kernel

theorem eligible039 : deductions039.all eligible = true := by
  simp only [deductions039, List.all_cons, List.all_nil, eligible, r3_mem, r4_mem, r5_mem,
    r6_mem, r9_mem, r10_mem, r11_mem, r12_mem, r13_mem, r14_mem, r16_mem, r17_mem, r18_mem,
    r19_mem, r20_mem, r22_mem, r23_mem, r24_mem, r25_mem, r26_mem, r27_mem, r29_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_039 :
    deductions039.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits039 =
      bits040 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
