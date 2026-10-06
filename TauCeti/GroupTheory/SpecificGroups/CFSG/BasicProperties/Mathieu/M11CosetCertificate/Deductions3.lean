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
# M11 coset certificate: Deductions3

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions048 : List (Fin 990 × List (Fin 4)) :=
  [(p623, r269), (p290, r270), (p72, r271), (p126, r272), (p189, r272), (p553, r272), (p85,
  r273), (p955, r274), (p245, r275), (p292, r276), (p97, r277), (p257, r277), (p304, r278),
  (p151, r279), (p403, r280), (p403, r281), (p621, r282), (p268, r283), (p334, r283), (p244,
  r284), (p759, r285), (p858, r286), (p599, r287), (p678, r288), (p589, r289), (p200, r290),
  (p422, r291), (p190, r292), (p263, r293), (p284, r294), (p468, r294), (p598, r294)]

@[expose]
def deductions049 : List (Fin 990 × List (Fin 4)) :=
  [(p487, r295), (p798, r296), (p206, r297), (p399, r297), (p728, r297), (p243, r298), (p362,
  r298), (p755, r298), (p726, r299), (p410, r300), (p87, r301), (p718, r302), (p192, r303),
  (p41, r304), (p199, r305), (p364, r305), (p551, r305), (p79, r306), (p598, r306), (p715,
  r307), (p747, r307), (p841, r307), (p111, r308), (p661, r308), (p912, r308), (p478, r309),
  (p783, r310), (p241, r311), (p906, r312), (p41, r313), (p160, r313), (p141, r314)]

@[expose]
def deductions050 : List (Fin 990 × List (Fin 4)) :=
  [(p735, r314), (p369, r315), (p442, r315), (p515, r315), (p608, r315), (p854, r315), (p193,
  r316), (p462, r316), (p937, r316), (p228, r317), (p188, r318), (p318, r318), (p389, r318),
  (p870, r318), (p346, r319), (p412, r319), (p508, r319), (p847, r320), (p908, r320), (p932,
  r320), (p947, r320), (p393, r321), (p597, r321), (p838, r321), (p929, r321), (p163, r322),
  (p296, r322), (p381, r322), (p284, r323), (p701, r324), (p658, r325), (p558, r326)]

@[expose]
def deductions051 : List (Fin 990 × List (Fin 4)) :=
  [(p593, r326), (p555, r327), (p604, r327), (p960, r327), (p413, r328), (p613, r328), (p874,
  r328), (p143, r329), (p484, r329), (p505, r329), (p771, r329), (p475, r330), (p374, r331),
  (p672, r332), (p876, r332), (p18, r333), (p224, r333), (p278, r333), (p745, r333), (p266,
  r334), (p813, r334), (p738, r335), (p906, r335), (p538, r336), (p977, r336), (p672, r337),
  (p746, r337), (p961, r337), (p599, r338), (p631, r338), (p551, r339), (p715, r339)]

@[expose]
def deductions052 : List (Fin 990 × List (Fin 4)) :=
  [(p73, r340), (p273, r340), (p306, r340), (p404, r340), (p661, r340), (p688, r340), (p190,
  r341), (p684, r341), (p771, r341), (p699, r342), (p417, r343), (p556, r343), (p580, r343),
  (p811, r343), (p400, r344), (p175, r345), (p287, r345), (p726, r345), (p554, r346), (p590,
  r346), (p134, r347), (p436, r347), (p700, r347), (p219, r348), (p471, r348), (p559, r348),
  (p661, r348), (p135, r349), (p309, r350), (p549, r351), (p979, r351), (p713, r352)]

@[expose]
def deductions053 : List (Fin 990 × List (Fin 4)) :=
  [(p955, r352), (p595, r353), (p829, r353), (p804, r354), (p605, r355), (p628, r355), (p401,
  r356), (p528, r356), (p318, r357), (p831, r358), (p266, r359), (p531, r360), (p288, r361),
  (p556, r362), (p557, r362), (p793, r362), (p207, r363), (p290, r363), (p199, r364), (p320,
  r364), (p442, r364), (p533, r364), (p662, r364), (p728, r364), (p157, r365), (p408, r365),
  (p489, r365), (p709, r365), (p303, r366), (p671, r366), (p48, r367), (p239, r367)]

@[expose]
def deductions054 : List (Fin 990 × List (Fin 4)) :=
  [(p429, r367), (p790, r367), (p580, r368), (p648, r368), (p784, r368), (p815, r368), (p735,
  r369), (p865, r369), (p490, r370), (p351, r371), (p715, r372), (p842, r372), (p210, r373),
  (p426, r374), (p795, r374), (p908, r375), (p944, r375), (p787, r376), (p390, r377), (p267,
  r378), (p208, r379), (p744, r379), (p332, r380), (p639, r380), (p366, r381), (p654, r381),
  (p778, r381), (p199, r382), (p460, r382), (p548, r382), (p672, r382), (p710, r382)]

@[expose]
def deductions055 : List (Fin 990 × List (Fin 4)) :=
  [(p937, r382), (p695, r383), (p965, r383), (p395, r384), (p399, r384), (p790, r384), (p883,
  r384), (p572, r385), (p903, r385), (p784, r386), (p309, r387), (p304, r388), (p557, r388),
  (p806, r388), (p853, r388), (p119, r389), (p679, r389), (p759, r390), (p100, r391), (p426,
  r391), (p478, r391), (p655, r391), (p394, r392), (p903, r393), (p695, r394), (p841, r394),
  (p855, r395), (p410, r396), (p503, r396), (p659, r396), (p754, r396), (p229, r397)]

@[expose]
def deductions056 : List (Fin 990 × List (Fin 4)) :=
  [(p195, r398), (p644, r398), (p165, r399), (p414, r399), (p487, r399), (p494, r399), (p193,
  r400), (p212, r400), (p347, r400), (p377, r400), (p387, r400), (p462, r400), (p704, r400),
  (p809, r400), (p813, r400), (p373, r401), (p486, r401), (p521, r401), (p564, r401), (p603,
  r401), (p639, r401), (p696, r401), (p714, r401), (p739, r401), (p919, r401), (p187, r402),
  (p198, r402), (p282, r402), (p373, r402), (p471, r402), (p521, r402), (p591, r402)]

@[expose]
def deductions057 : List (Fin 990 × List (Fin 4)) :=
  [(p637, r402), (p641, r402), (p238, r403), (p500, r403), (p826, r403), (p181, r404), (p501,
  r404), (p707, r404), (p375, r405), (p401, r406), (p606, r406), (p287, r407), (p339, r407),
  (p352, r407), (p425, r407), (p639, r407), (p406, r408), (p438, r408), (p498, r408), (p699,
  r408), (p784, r408), (p313, r409), (p743, r409), (p785, r409), (p541, r410), (p592, r410),
  (p467, r411), (p231, r412), (p437, r412), (p464, r412), (p742, r412), (p463, r413)]

@[expose]
def deductions058 : List (Fin 990 × List (Fin 4)) :=
  [(p488, r413), (p515, r413), (p642, r413), (p854, r413), (p124, r414), (p218, r414), (p335,
  r414), (p685, r414), (p725, r414), (p931, r414), (p196, r415), (p237, r415), (p334, r415),
  (p380, r415), (p590, r415), (p609, r415), (p652, r415), (p653, r415), (p718, r415), (p739,
  r415), (p902, r415), (p904, r415), (p907, r415), (p155, r416), (p167, r416), (p302, r416),
  (p365, r416), (p458, r416), (p602, r416), (p294, r417), (p309, r417), (p683, r417)]

@[expose]
def deductions059 : List (Fin 990 × List (Fin 4)) :=
  [(p251, r418), (p257, r418), (p727, r418), (p315, r419), (p575, r419), (p606, r420), (p644,
  r420), (p845, r420), (p846, r420), (p947, r420), (p382, r421), (p698, r421), (p946, r421),
  (p315, r422), (p331, r422), (p343, r422), (p472, r422), (p527, r422), (p552, r422), (p738,
  r422), (p267, r423), (p437, r423), (p720, r423), (p789, r423), (p806, r423), (p978, r423),
  (p209, r424), (p218, r424), (p712, r424), (p728, r424), (p831, r424), (p860, r424)]

@[expose]
def deductions060 : List (Fin 990 × List (Fin 4)) :=
  [(p891, r424), (p892, r424), (p636, r425), (p798, r425), (p348, r426), (p494, r426), (p869,
  r426), (p671, r427), (p703, r427), (p165, r428), (p291, r428), (p361, r428), (p692, r428),
  (p729, r428), (p732, r428), (p966, r428), (p971, r428), (p480, r429), (p559, r429), (p568,
  r429), (p943, r429), (p394, r430), (p503, r430), (p523, r430), (p573, r430), (p931, r431),
  (p56, r432), (p637, r433), (p646, r433), (p887, r433), (p411, r434), (p615, r434)]

@[expose]
def deductions061 : List (Fin 990 × List (Fin 4)) :=
  [(p666, r434), (p759, r434), (p797, r434), (p799, r434), (p838, r434), (p281, r435), (p573,
  r435), (p600, r435), (p269, r436), (p464, r436), (p568, r436), (p687, r436), (p696, r436),
  (p755, r436), (p760, r436), (p827, r436), (p904, r436), (p946, r436), (p971, r436), (p979,
  r436), (p213, r437), (p351, r437), (p605, r437), (p669, r437), (p783, r437), (p285, r438),
  (p615, r438), (p634, r438), (p829, r438), (p182, r439), (p373, r439), (p403, r439)]

@[expose]
def deductions062 : List (Fin 990 × List (Fin 4)) :=
  [(p490, r439), (p597, r439), (p617, r439), (p633, r439), (p637, r439), (p646, r439), (p768,
  r439), (p790, r439), (p793, r439), (p810, r439), (p825, r439), (p953, r439), (p960, r439),
  (p809, r440), (p335, r441), (p448, r441), (p611, r441), (p725, r441), (p814, r441), (p821,
  r441), (p924, r441), (p546, r442), (p663, r442), (p43, r443), (p469, r443), (p857, r443),
  (p424, r444), (p981, r444), (p270, r445), (p294, r445), (p357, r445), (p719, r445)]

@[expose]
def deductions063 : List (Fin 990 × List (Fin 4)) :=
  [(p160, r446), (p253, r446), (p955, r446), (p976, r446), (p231, r447), (p466, r447), (p485,
  r447), (p529, r447), (p629, r447), (p660, r447), (p880, r447), (p949, r447), (p341, r448),
  (p516, r448), (p734, r448), (p56, r449), (p268, r449), (p505, r449), (p571, r449), (p704,
  r449), (p751, r449), (p798, r449), (p851, r449), (p905, r449), (p494, r450), (p498, r450),
  (p547, r450), (p743, r450), (p885, r450), (p952, r450), (p414, r451), (p619, r451)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
