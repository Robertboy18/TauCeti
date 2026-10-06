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
# M11 coset certificate: Deductions0

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions000 : List (Fin 990 × List (Fin 4)) :=
  [(p0, r0), (p2, r0), (p3, r0), (p5, r0), (p6, r0), (p8, r0), (p9, r0), (p10, r0), (p11, r0),
  (p13, r0), (p14, r0), (p16, r0), (p17, r0), (p19, r0), (p20, r0), (p22, r0), (p23, r0), (p26,
  r0), (p27, r0), (p28, r0), (p29, r0), (p30, r0), (p31, r0), (p32, r0), (p34, r0), (p35, r0),
  (p37, r0), (p38, r0), (p40, r0), (p41, r0), (p42, r0), (p43, r0)]

@[expose]
def deductions001 : List (Fin 990 × List (Fin 4)) :=
  [(p45, r0), (p48, r0), (p49, r0), (p51, r0), (p52, r0), (p54, r0), (p56, r0), (p57, r0), (p59,
  r0), (p60, r0), (p63, r0), (p65, r0), (p66, r0), (p67, r0), (p70, r0), (p71, r0), (p75, r0),
  (p76, r0), (p78, r0), (p80, r0), (p81, r0), (p82, r0), (p84, r0), (p85, r0), (p87, r0), (p88,
  r0), (p89, r0), (p90, r0), (p92, r0), (p94, r0), (p95, r0), (p96, r0)]

@[expose]
def deductions002 : List (Fin 990 × List (Fin 4)) :=
  [(p99, r0), (p101, r0), (p102, r0), (p104, r0), (p105, r0), (p106, r0), (p109, r0), (p110,
  r0), (p112, r0), (p113, r0), (p114, r0), (p115, r0), (p116, r0), (p118, r0), (p120, r0),
  (p121, r0), (p123, r0), (p124, r0), (p126, r0), (p128, r0), (p129, r0), (p131, r0), (p134,
  r0), (p136, r0), (p137, r0), (p138, r0), (p139, r0), (p141, r0), (p142, r0), (p144, r0),
  (p145, r0), (p147, r0)]

@[expose]
def deductions003 : List (Fin 990 × List (Fin 4)) :=
  [(p148, r0), (p150, r0), (p152, r0), (p153, r0), (p156, r0), (p157, r0), (p158, r0), (p159,
  r0), (p162, r0), (p163, r0), (p168, r0), (p171, r0), (p174, r0), (p178, r0), (p180, r0),
  (p182, r0), (p183, r0), (p185, r0), (p186, r0), (p189, r0), (p191, r0), (p194, r0), (p195,
  r0), (p197, r0), (p200, r0), (p203, r0), (p205, r0), (p206, r0), (p208, r0), (p210, r0),
  (p211, r0), (p213, r0)]

@[expose]
def deductions004 : List (Fin 990 × List (Fin 4)) :=
  [(p214, r0), (p216, r0), (p217, r0), (p220, r0), (p222, r0), (p224, r0), (p225, r0), (p232,
  r0), (p233, r0), (p235, r0), (p236, r0), (p239, r0), (p242, r0), (p244, r0), (p245, r0),
  (p246, r0), (p247, r0), (p255, r0), (p256, r0), (p258, r0), (p260, r0), (p264, r0), (p265,
  r0), (p268, r0), (p269, r0), (p271, r0), (p273, r0), (p276, r0), (p278, r0), (p279, r0),
  (p281, r0), (p286, r0)]

@[expose]
def deductions005 : List (Fin 990 × List (Fin 4)) :=
  [(p289, r0), (p291, r0), (p293, r0), (p298, r0), (p299, r0), (p300, r0), (p304, r0), (p307,
  r0), (p310, r0), (p317, r0), (p320, r0), (p321, r0), (p324, r0), (p326, r0), (p330, r0),
  (p333, r0), (p338, r0), (p344, r0), (p347, r0), (p349, r0), (p350, r0), (p353, r0), (p357,
  r0), (p360, r0), (p367, r0), (p369, r0), (p370, r0), (p374, r0), (p375, r0), (p376, r0),
  (p378, r0), (p379, r0)]

@[expose]
def deductions006 : List (Fin 990 × List (Fin 4)) :=
  [(p383, r0), (p386, r0), (p387, r0), (p390, r0), (p391, r0), (p396, r0), (p398, r0), (p400,
  r0), (p405, r0), (p406, r0), (p407, r0), (p409, r0), (p419, r0), (p423, r0), (p424, r0),
  (p430, r0), (p432, r0), (p433, r0), (p441, r0), (p445, r0), (p456, r0), (p464, r0), (p469,
  r0), (p479, r0), (p483, r0), (p491, r0), (p497, r0), (p510, r0), (p511, r0), (p520, r0),
  (p522, r0), (p530, r0)]

@[expose]
def deductions007 : List (Fin 990 × List (Fin 4)) :=
  [(p531, r0), (p533, r0), (p536, r0), (p538, r0), (p540, r0), (p554, r0), (p555, r0), (p560,
  r0), (p570, r0), (p577, r0), (p579, r0), (p604, r0), (p610, r0), (p624, r0), (p627, r0),
  (p662, r0), (p680, r0), (p691, r0), (p757, r0), (p767, r0), (p775, r0), (p779, r0), (p824,
  r0), (p867, r0), (p940, r0), (p1, r1), (p3, r1), (p4, r1), (p6, r1), (p7, r1), (p9, r1), (p10,
  r1)]

@[expose]
def deductions008 : List (Fin 990 × List (Fin 4)) :=
  [(p11, r1), (p12, r1), (p14, r1), (p15, r1), (p17, r1), (p19, r1), (p20, r1), (p21, r1), (p23,
  r1), (p24, r1), (p26, r1), (p28, r1), (p29, r1), (p31, r1), (p32, r1), (p33, r1), (p34, r1),
  (p36, r1), (p38, r1), (p39, r1), (p42, r1), (p44, r1), (p46, r1), (p47, r1), (p49, r1), (p51,
  r1), (p52, r1), (p53, r1), (p57, r1), (p58, r1), (p59, r1), (p61, r1)]

@[expose]
def deductions009 : List (Fin 990 × List (Fin 4)) :=
  [(p63, r1), (p66, r1), (p67, r1), (p68, r1), (p69, r1), (p71, r1), (p75, r1), (p76, r1), (p77,
  r1), (p79, r1), (p81, r1), (p82, r1), (p83, r1), (p86, r1), (p88, r1), (p89, r1), (p91, r1),
  (p92, r1), (p93, r1), (p95, r1), (p96, r1), (p97, r1), (p98, r1), (p99, r1), (p100, r1),
  (p102, r1), (p103, r1), (p105, r1), (p106, r1), (p107, r1), (p108, r1), (p110, r1)]

@[expose]
def deductions010 : List (Fin 990 × List (Fin 4)) :=
  [(p113, r1), (p114, r1), (p115, r1), (p116, r1), (p119, r1), (p121, r1), (p124, r1), (p125,
  r1), (p127, r1), (p129, r1), (p131, r1), (p135, r1), (p138, r1), (p139, r1), (p140, r1),
  (p145, r1), (p150, r1), (p151, r1), (p153, r1), (p154, r1), (p156, r1), (p159, r1), (p161,
  r1), (p167, r1), (p168, r1), (p169, r1), (p172, r1), (p174, r1), (p175, r1), (p177, r1),
  (p178, r1), (p186, r1)]

@[expose]
def deductions011 : List (Fin 990 × List (Fin 4)) :=
  [(p188, r1), (p193, r1), (p196, r1), (p197, r1), (p201, r1), (p204, r1), (p207, r1), (p210,
  r1), (p215, r1), (p218, r1), (p219, r1), (p221, r1), (p222, r1), (p223, r1), (p227, r1),
  (p229, r1), (p230, r1), (p231, r1), (p233, r1), (p234, r1), (p235, r1), (p238, r1), (p242,
  r1), (p246, r1), (p247, r1), (p249, r1), (p250, r1), (p254, r1), (p256, r1), (p258, r1),
  (p262, r1), (p265, r1)]

@[expose]
def deductions012 : List (Fin 990 × List (Fin 4)) :=
  [(p270, r1), (p272, r1), (p274, r1), (p276, r1), (p277, r1), (p280, r1), (p286, r1), (p290,
  r1), (p292, r1), (p293, r1), (p294, r1), (p295, r1), (p297, r1), (p303, r1), (p305, r1),
  (p308, r1), (p311, r1), (p313, r1), (p314, r1), (p315, r1), (p321, r1), (p324, r1), (p325,
  r1), (p326, r1), (p327, r1), (p328, r1), (p330, r1), (p331, r1), (p332, r1), (p342, r1),
  (p343, r1), (p346, r1)]

@[expose]
def deductions013 : List (Fin 990 × List (Fin 4)) :=
  [(p347, r1), (p348, r1), (p353, r1), (p363, r1), (p367, r1), (p371, r1), (p377, r1), (p384,
  r1), (p390, r1), (p391, r1), (p392, r1), (p396, r1), (p408, r1), (p411, r1), (p412, r1),
  (p417, r1), (p420, r1), (p423, r1), (p424, r1), (p426, r1), (p427, r1), (p430, r1), (p432,
  r1), (p433, r1), (p434, r1), (p436, r1), (p437, r1), (p438, r1), (p440, r1), (p443, r1),
  (p450, r1), (p452, r1)]

@[expose]
def deductions014 : List (Fin 990 × List (Fin 4)) :=
  [(p455, r1), (p465, r1), (p466, r1), (p470, r1), (p473, r1), (p485, r1), (p488, r1), (p491,
  r1), (p496, r1), (p500, r1), (p508, r1), (p510, r1), (p511, r1), (p512, r1), (p514, r1),
  (p516, r1), (p530, r1), (p549, r1), (p552, r1), (p555, r1), (p562, r1), (p564, r1), (p566,
  r1), (p569, r1), (p585, r1), (p601, r1), (p610, r1), (p611, r1), (p612, r1), (p626, r1),
  (p632, r1), (p636, r1)]

@[expose]
def deductions015 : List (Fin 990 × List (Fin 4)) :=
  [(p659, r1), (p663, r1), (p676, r1), (p683, r1), (p688, r1), (p692, r1), (p708, r1), (p733,
  r1), (p734, r1), (p758, r1), (p800, r1), (p889, r1), (p0, r2), (p1, r2), (p2, r2), (p4, r2),
  (p5, r2), (p6, r2), (p7, r2), (p8, r2), (p11, r2), (p12, r2), (p13, r2), (p15, r2), (p16, r2),
  (p18, r2), (p20, r2), (p21, r2), (p22, r2), (p24, r2), (p25, r2), (p27, r2)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
