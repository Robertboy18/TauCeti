/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Points0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Points1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Points2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Points3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Relators0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Relators1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Relators2

/-!
# M11 coset certificate: Deductions2

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions032 : List (Fin 990 × List (Fin 4)) :=
  [(p483, r11), (p689, r11), (p774, r11), (p897, r11), (p143, r12), (p498, r12), (p703, r12),
  (p898, r12), (p38, r13), (p102, r13), (p163, r13), (p253, r13), (p302, r13), (p396, r13),
  (p596, r13), (p814, r13), (p166, r14), (p306, r14), (p358, r14), (p442, r14), (p744, r14),
  (p866, r14), (p317, r15), (p604, r15), (p746, r15), (p243, r16), (p386, r16), (p560, r16),
  (p60, r17), (p180, r17), (p271, r17), (p410, r17)]

@[expose]
def deductions033 : List (Fin 990 × List (Fin 4)) :=
  [(p575, r17), (p677, r17), (p794, r18), (p959, r18), (p535, r19), (p154, r20), (p297, r20),
  (p434, r20), (p505, r20), (p591, r20), (p710, r20), (p857, r20), (p882, r20), (p884, r20),
  (p453, r21), (p671, r21), (p960, r21), (p240, r22), (p774, r22), (p141, r24), (p574, r24),
  (p431, r26), (p563, r26), (p886, r26), (p94, r27), (p216, r27), (p349, r27), (p493, r27),
  (p146, r28), (p125, r30), (p277, r30), (p943, r30)]

@[expose]
def deductions034 : List (Fin 990 × List (Fin 4)) :=
  [(p64, r31), (p122, r31), (p184, r31), (p322, r31), (p648, r31), (p640, r32), (p278, r33),
  (p605, r33), (p176, r34), (p429, r34), (p454, r34), (p673, r34), (p846, r34), (p529, r35),
  (p775, r35), (p84, r37), (p359, r37), (p427, r39), (p528, r39), (p202, r40), (p336, r40),
  (p481, r40), (p691, r40), (p717, r41), (p340, r46), (p172, r47), (p366, r54), (p542, r54),
  (p617, r55), (p467, r56), (p474, r59), (p545, r60)]

@[expose]
def deductions035 : List (Fin 990 × List (Fin 4)) :=
  [(p240, r61), (p977, r61), (p367, r62), (p420, r64), (p221, r65), (p513, r65), (p724, r66),
  (p792, r77), (p248, r88), (p382, r89), (p412, r90), (p316, r91), (p603, r96), (p825, r97),
  (p641, r111), (p884, r113), (p640, r121), (p550, r140), (p623, r140), (p457, r142), (p657,
  r143), (p377, r145), (p890, r145), (p917, r164), (p782, r171), (p769, r175), (p917, r202),
  (p944, r239), (p916, r240), (p938, r322), (p741, r336), (p873, r543)]

@[expose]
def deductions036 : List (Fin 990 × List (Fin 4)) :=
  [(p817, r544), (p951, r544), (p580, r545), (p916, r545), (p676, r546), (p202, r547), (p336,
  r547), (p667, r548), (p509, r549), (p693, r549), (p421, r550), (p848, r551), (p543, r552),
  (p574, r553), (p506, r554), (p746, r554), (p949, r555), (p374, r556), (p628, r556), (p816,
  r557), (p923, r558), (p610, r559), (p783, r560), (p895, r561), (p794, r562), (p909, r563),
  (p630, r564), (p956, r565), (p862, r566), (p402, r567), (p577, r568), (p682, r569)]

@[expose]
def deductions037 : List (Fin 990 × List (Fin 4)) :=
  [(p592, r570), (p463, r571), (p513, r572), (p857, r573), (p620, r574), (p717, r575), (p961,
  r576), (p854, r577), (p622, r578), (p443, r579), (p515, r580), (p435, r581), (p927, r582),
  (p936, r583), (p332, r584), (p634, r585), (p724, r586), (p472, r587), (p345, r588), (p726,
  r589), (p909, r590), (p635, r591), (p705, r592), (p598, r593), (p908, r594), (p873, r595),
  (p743, r596), (p809, r597), (p941, r598), (p973, r599), (p849, r600), (p804, r601)]

@[expose]
def deductions038 : List (Fin 990 × List (Fin 4)) :=
  [(p684, r602), (p885, r603), (p926, r604), (p456, r605), (p482, r606), (p311, r607), (p362,
  r608), (p875, r609), (p801, r610), (p851, r611), (p840, r612), (p630, r613), (p779, r614),
  (p721, r615), (p649, r616), (p736, r617), (p653, r618), (p832, r619), (p635, r620), (p492,
  r621), (p319, r622), (p507, r623), (p723, r624), (p697, r625), (p614, r626), (p950, r627),
  (p793, r628), (p871, r629), (p589, r630), (p602, r631), (p0, [1, 2]), (p344, r1)]

@[expose]
def deductions039 : List (Fin 990 × List (Fin 4)) :=
  [(p3, r3), (p74, r4), (p695, r4), (p79, r5), (p31, r6), (p329, r9), (p25, r10), (p284, r11),
  (p697, r11), (p608, r12), (p14, r13), (p211, r14), (p189, r16), (p35, r17), (p90, r18), (p293,
  r18), (p98, r19), (p679, r19), (p93, r20), (p612, r20), (p148, r22), (p107, r23), (p451, r23),
  (p84, r24), (p855, r24), (p97, r25), (p233, r25), (p553, r26), (p520, r27), (p23, r29), (p222,
  r29), (p753, r29)]

@[expose]
def deductions040 : List (Fin 990 × List (Fin 4)) :=
  [(p306, r30), (p46, r32), (p177, r32), (p644, r34), (p227, r36), (p251, r36), (p34, r37),
  (p663, r37), (p55, r38), (p299, r38), (p86, r39), (p223, r39), (p368, r39), (p226, r41),
  (p422, r42), (p179, r43), (p658, r43), (p126, r44), (p80, r45), (p291, r48), (p208, r49),
  (p366, r50), (p417, r50), (p801, r50), (p787, r51), (p316, r52), (p133, r53), (p190, r57),
  (p321, r58), (p501, r61), (p333, r63), (p55, r67)]

@[expose]
def deductions041 : List (Fin 990 × List (Fin 4)) :=
  [(p314, r67), (p478, r68), (p596, r69), (p308, r70), (p388, r71), (p333, r72), (p647, r73),
  (p803, r74), (p339, r75), (p520, r76), (p211, r78), (p164, r79), (p689, r80), (p337, r81),
  (p660, r82), (p741, r83), (p136, r84), (p435, r85), (p847, r86), (p229, r87), (p670, r91),
  (p688, r91), (p368, r92), (p950, r92), (p142, r93), (p926, r94), (p709, r95), (p596, r97),
  (p477, r98), (p678, r99), (p334, r100), (p869, r101)]

@[expose]
def deductions042 : List (Fin 990 × List (Fin 4)) :=
  [(p563, r102), (p50, r103), (p685, r104), (p504, r105), (p235, r106), (p357, r107), (p247,
  r108), (p705, r109), (p32, r110), (p91, r112), (p694, r114), (p704, r114), (p257, r115),
  (p480, r116), (p461, r117), (p203, r118), (p335, r118), (p534, r119), (p664, r119), (p589,
  r120), (p60, r122), (p666, r123), (p810, r123), (p479, r124), (p356, r125), (p616, r125),
  (p459, r126), (p527, r127), (p391, r128), (p716, r129), (p542, r130), (p606, r131)]

@[expose]
def deductions043 : List (Fin 990 × List (Fin 4)) :=
  [(p670, r132), (p512, r133), (p716, r134), (p697, r135), (p476, r136), (p723, r137), (p753,
  r138), (p645, r139), (p730, r140), (p834, r141), (p772, r142), (p982, r144), (p535, r145),
  (p837, r146), (p405, r147), (p964, r148), (p397, r149), (p804, r150), (p887, r151), (p752,
  r152), (p952, r153), (p723, r154), (p971, r155), (p629, r156), (p731, r157), (p561, r158),
  (p493, r159), (p319, r160), (p673, r160), (p295, r161), (p601, r161), (p686, r162)]

@[expose]
def deductions044 : List (Fin 990 × List (Fin 4)) :=
  [(p678, r163), (p583, r164), (p770, r165), (p337, r166), (p545, r167), (p601, r168), (p624,
  r168), (p616, r169), (p836, r169), (p361, r170), (p799, r170), (p302, r171), (p307, r171),
  (p602, r171), (p861, r172), (p159, r173), (p645, r174), (p724, r174), (p267, r175), (p465,
  r176), (p614, r177), (p665, r178), (p583, r179), (p686, r180), (p727, r181), (p686, r182),
  (p666, r183), (p909, r184), (p635, r185), (p553, r186), (p574, r187), (p276, r188)]

@[expose]
def deductions045 : List (Fin 990 × List (Fin 4)) :=
  [(p117, r189), (p289, r190), (p475, r191), (p552, r192), (p378, r193), (p712, r194), (p355,
  r195), (p354, r196), (p550, r197), (p668, r198), (p752, r199), (p696, r200), (p732, r200),
  (p477, r201), (p950, r203), (p713, r204), (p646, r205), (p714, r205), (p677, r206), (p906,
  r206), (p305, r207), (p729, r208), (p405, r209), (p692, r210), (p451, r211), (p756, r212),
  (p869, r213), (p756, r214), (p713, r215), (p296, r216), (p721, r217), (p953, r217)]

@[expose]
def deductions046 : List (Fin 990 × List (Fin 4)) :=
  [(p717, r218), (p750, r219), (p558, r220), (p969, r220), (p634, r221), (p859, r222), (p345,
  r223), (p474, r224), (p418, r225), (p684, r226), (p274, r227), (p158, r228), (p968, r229),
  (p493, r230), (p542, r231), (p750, r232), (p877, r232), (p68, r233), (p149, r233), (p623,
  r233), (p837, r234), (p754, r235), (p62, r236), (p170, r237), (p344, r238), (p328, r239),
  (p631, r239), (p492, r241), (p358, r242), (p788, r242), (p220, r243), (p429, r244)]

@[expose]
def deductions047 : List (Fin 990 × List (Fin 4)) :=
  [(p133, r245), (p625, r246), (p65, r247), (p685, r248), (p778, r248), (p248, r249), (p778,
  r250), (p209, r251), (p805, r252), (p134, r253), (p670, r253), (p817, r254), (p474, r255),
  (p887, r256), (p970, r256), (p288, r257), (p700, r258), (p472, r259), (p800, r259), (p471,
  r260), (p756, r261), (p253, r262), (p811, r263), (p272, r264), (p631, r264), (p883, r265),
  (p799, r266), (p252, r267), (p459, r267), (p173, r268), (p841, r268), (p42, r269)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
