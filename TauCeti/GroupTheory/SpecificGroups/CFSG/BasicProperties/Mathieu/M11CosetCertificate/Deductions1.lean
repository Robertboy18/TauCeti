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
# M11 coset certificate: Deductions1

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions016 : List (Fin 990 × List (Fin 4)) :=
  [(p29, r2), (p30, r2), (p33, r2), (p35, r2), (p36, r2), (p37, r2), (p39, r2), (p40, r2), (p43,
  r2), (p44, r2), (p45, r2), (p46, r2), (p47, r2), (p50, r2), (p52, r2), (p53, r2), (p54, r2),
  (p57, r2), (p58, r2), (p61, r2), (p62, r2), (p63, r2), (p64, r2), (p68, r2), (p69, r2), (p70,
  r2), (p71, r2), (p72, r2), (p74, r2), (p76, r2), (p77, r2), (p78, r2)]

@[expose]
def deductions017 : List (Fin 990 × List (Fin 4)) :=
  [(p82, r2), (p83, r2), (p85, r2), (p86, r2), (p87, r2), (p92, r2), (p95, r2), (p101, r2),
  (p103, r2), (p104, r2), (p107, r2), (p108, r2), (p109, r2), (p110, r2), (p111, r2), (p112,
  r2), (p116, r2), (p117, r2), (p119, r2), (p120, r2), (p121, r2), (p122, r2), (p123, r2),
  (p125, r2), (p127, r2), (p128, r2), (p129, r2), (p130, r2), (p132, r2), (p137, r2), (p139,
  r2), (p140, r2)]

@[expose]
def deductions018 : List (Fin 990 × List (Fin 4)) :=
  [(p142, r2), (p143, r2), (p144, r2), (p145, r2), (p146, r2), (p147, r2), (p149, r2), (p151,
  r2), (p153, r2), (p155, r2), (p156, r2), (p161, r2), (p162, r2), (p164, r2), (p166, r2),
  (p168, r2), (p169, r2), (p170, r2), (p171, r2), (p173, r2), (p175, r2), (p176, r2), (p178,
  r2), (p179, r2), (p180, r2), (p181, r2), (p182, r2), (p183, r2), (p184, r2), (p185, r2),
  (p187, r2), (p191, r2)]

@[expose]
def deductions019 : List (Fin 990 × List (Fin 4)) :=
  [(p192, r2), (p194, r2), (p195, r2), (p197, r2), (p198, r2), (p201, r2), (p203, r2), (p204,
  r2), (p207, r2), (p214, r2), (p215, r2), (p217, r2), (p219, r2), (p223, r2), (p225, r2),
  (p227, r2), (p228, r2), (p230, r2), (p232, r2), (p236, r2), (p237, r2), (p241, r2), (p243,
  r2), (p244, r2), (p246, r2), (p249, r2), (p251, r2), (p252, r2), (p254, r2), (p255, r2),
  (p258, r2), (p260, r2)]

@[expose]
def deductions020 : List (Fin 990 × List (Fin 4)) :=
  [(p262, r2), (p266, r2), (p269, r2), (p270, r2), (p271, r2), (p272, r2), (p275, r2), (p277,
  r2), (p279, r2), (p280, r2), (p282, r2), (p283, r2), (p285, r2), (p287, r2), (p296, r2),
  (p301, r2), (p303, r2), (p308, r2), (p310, r2), (p312, r2), (p316, r2), (p317, r2), (p320,
  r2), (p322, r2), (p325, r2), (p327, r2), (p329, r2), (p331, r2), (p337, r2), (p338, r2),
  (p341, r2), (p345, r2)]

@[expose]
def deductions021 : List (Fin 990 × List (Fin 4)) :=
  [(p348, r2), (p350, r2), (p352, r2), (p354, r2), (p355, r2), (p360, r2), (p362, r2), (p368,
  r2), (p370, r2), (p372, r2), (p379, r2), (p381, r2), (p386, r2), (p389, r2), (p392, r2),
  (p393, r2), (p398, r2), (p401, r2), (p402, r2), (p407, r2), (p413, r2), (p415, r2), (p419,
  r2), (p425, r2), (p427, r2), (p439, r2), (p444, r2), (p447, r2), (p453, r2), (p454, r2),
  (p458, r2), (p468, r2)]

@[expose]
def deductions022 : List (Fin 990 × List (Fin 4)) :=
  [(p477, r2), (p482, r2), (p484, r2), (p487, r2), (p496, r2), (p507, r2), (p510, r2), (p514,
  r2), (p517, r2), (p523, r2), (p525, r2), (p527, r2), (p528, r2), (p531, r2), (p537, r2),
  (p539, r2), (p543, r2), (p549, r2), (p558, r2), (p565, r2), (p572, r2), (p576, r2), (p586,
  r2), (p620, r2), (p640, r2), (p642, r2), (p653, r2), (p657, r2), (p660, r2), (p665, r2),
  (p669, r2), (p681, r2)]

@[expose]
def deductions023 : List (Fin 990 × List (Fin 4)) :=
  [(p727, r2), (p731, r2), (p752, r2), (p764, r2), (p785, r2), (p834, r2), (p927, r2), (p0, r3),
  (p1, r3), (p2, r3), (p4, r3), (p5, r3), (p7, r3), (p8, r3), (p9, r3), (p10, r3), (p12, r3),
  (p13, r3), (p15, r3), (p16, r3), (p17, r3), (p18, r3), (p19, r3), (p21, r3), (p22, r3), (p24,
  r3), (p25, r3), (p26, r3), (p27, r3), (p28, r3), (p30, r3), (p33, r3)]

@[expose]
def deductions024 : List (Fin 990 × List (Fin 4)) :=
  [(p36, r3), (p37, r3), (p39, r3), (p40, r3), (p44, r3), (p45, r3), (p47, r3), (p48, r3), (p49,
  r3), (p50, r3), (p51, r3), (p53, r3), (p54, r3), (p55, r3), (p58, r3), (p59, r3), (p61, r3),
  (p62, r3), (p64, r3), (p65, r3), (p66, r3), (p67, r3), (p69, r3), (p70, r3), (p72, r3), (p73,
  r3), (p74, r3), (p75, r3), (p77, r3), (p78, r3), (p80, r3), (p83, r3)]

@[expose]
def deductions025 : List (Fin 990 × List (Fin 4)) :=
  [(p88, r3), (p89, r3), (p91, r3), (p93, r3), (p94, r3), (p96, r3), (p98, r3), (p100, r3),
  (p101, r3), (p103, r3), (p104, r3), (p106, r3), (p108, r3), (p111, r3), (p112, r3), (p113,
  r3), (p114, r3), (p115, r3), (p117, r3), (p118, r3), (p120, r3), (p122, r3), (p123, r3),
  (p127, r3), (p128, r3), (p130, r3), (p132, r3), (p133, r3), (p135, r3), (p136, r3), (p137,
  r3), (p140, r3)]

@[expose]
def deductions026 : List (Fin 990 × List (Fin 4)) :=
  [(p144, r3), (p146, r3), (p147, r3), (p148, r3), (p149, r3), (p150, r3), (p152, r3), (p154,
  r3), (p155, r3), (p157, r3), (p158, r3), (p160, r3), (p161, r3), (p162, r3), (p164, r3),
  (p165, r3), (p166, r3), (p167, r3), (p170, r3), (p171, r3), (p172, r3), (p173, r3), (p174,
  r3), (p176, r3), (p177, r3), (p179, r3), (p181, r3), (p184, r3), (p185, r3), (p186, r3),
  (p187, r3), (p188, r3)]

@[expose]
def deductions027 : List (Fin 990 × List (Fin 4)) :=
  [(p191, r3), (p194, r3), (p198, r3), (p201, r3), (p202, r3), (p204, r3), (p206, r3), (p209,
  r3), (p212, r3), (p213, r3), (p215, r3), (p220, r3), (p221, r3), (p224, r3), (p225, r3),
  (p226, r3), (p237, r3), (p239, r3), (p240, r3), (p241, r3), (p242, r3), (p245, r3), (p248,
  r3), (p250, r3), (p252, r3), (p254, r3), (p262, r3), (p263, r3), (p264, r3), (p265, r3),
  (p273, r3), (p280, r3)]

@[expose]
def deductions028 : List (Fin 990 × List (Fin 4)) :=
  [(p283, r3), (p286, r3), (p288, r3), (p292, r3), (p295, r3), (p298, r3), (p301, r3), (p305,
  r3), (p307, r3), (p313, r3), (p314, r3), (p319, r3), (p323, r3), (p324, r3), (p325, r3),
  (p326, r3), (p336, r3), (p339, r3), (p340, r3), (p342, r3), (p343, r3), (p346, r3), (p349,
  r3), (p351, r3), (p355, r3), (p356, r3), (p358, r3), (p363, r3), (p365, r3), (p371, r3),
  (p375, r3), (p378, r3)]

@[expose]
def deductions029 : List (Fin 990 × List (Fin 4)) :=
  [(p380, r3), (p385, r3), (p387, r3), (p389, r3), (p394, r3), (p395, r3), (p398, r3), (p399,
  r3), (p400, r3), (p404, r3), (p408, r3), (p411, r3), (p413, r3), (p420, r3), (p421, r3),
  (p428, r3), (p432, r3), (p435, r3), (p436, r3), (p444, r3), (p447, r3), (p452, r3), (p453,
  r3), (p458, r3), (p459, r3), (p465, r3), (p466, r3), (p468, r3), (p479, r3), (p488, r3),
  (p496, r3), (p501, r3)]

@[expose]
def deductions030 : List (Fin 990 × List (Fin 4)) :=
  [(p508, r3), (p511, r3), (p513, r3), (p517, r3), (p518, r3), (p523, r3), (p525, r3), (p543,
  r3), (p550, r3), (p556, r3), (p567, r3), (p569, r3), (p571, r3), (p576, r3), (p579, r3),
  (p584, r3), (p587, r3), (p588, r3), (p619, r3), (p649, r3), (p658, r3), (p682, r3), (p687,
  r3), (p744, r3), (p751, r3), (p775, r3), (p795, r3), (p827, r3), (p891, r3), (p132, r4),
  (p285, r4), (p418, r4)]

@[expose]
def deductions031 : List (Fin 990 × List (Fin 4)) :=
  [(p484, r4), (p582, r4), (p690, r4), (p853, r4), (p519, r5), (p81, r6), (p196, r6), (p289,
  r6), (p423, r6), (p585, r6), (p680, r6), (p228, r7), (p370, r7), (p551, r7), (p341, r8),
  (p620, r8), (p753, r8), (p205, r9), (p338, r9), (p369, r9), (p463, r9), (p750, r9), (p879,
  r9), (p73, r10), (p130, r10), (p192, r10), (p283, r10), (p329, r10), (p416, r10), (p614, r10),
  (p823, r10), (p131, r11)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
