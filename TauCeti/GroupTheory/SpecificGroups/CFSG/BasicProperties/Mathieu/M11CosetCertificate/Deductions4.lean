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
# M11 coset certificate: Deductions4

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions064 : List (Fin 990 × List (Fin 4)) :=
  [(p667, r451), (p682, r451), (p721, r451), (p380, r452), (p460, r452), (p595, r452), (p787,
  r452), (p976, r452), (p234, r453), (p406, r453), (p587, r453), (p618, r453), (p850, r453),
  (p912, r453), (p568, r454), (p625, r454), (p643, r454), (p656, r454), (p791, r454), (p792,
  r454), (p813, r454), (p885, r454), (p934, r454), (p942, r454), (p951, r454), (p706, r455),
  (p972, r455), (p588, r456), (p801, r456), (p849, r456), (p926, r456), (p674, r457)]

@[expose]
def deductions065 : List (Fin 990 × List (Fin 4)) :=
  [(p780, r457), (p794, r457), (p216, r458), (p641, r458), (p811, r458), (p855, r458), (p919,
  r458), (p946, r458), (p421, r459), (p489, r459), (p514, r459), (p561, r459), (p693, r459),
  (p118, r460), (p279, r460), (p365, r460), (p388, r460), (p483, r460), (p519, r460), (p962,
  r460), (p461, r461), (p911, r461), (p384, r462), (p457, r462), (p687, r462), (p716, r462),
  (p871, r462), (p979, r462), (p301, r463), (p404, r463), (p419, r463), (p480, r463)]

@[expose]
def deductions066 : List (Fin 990 × List (Fin 4)) :=
  [(p931, r463), (p951, r463), (p433, r464), (p506, r464), (p632, r464), (p792, r464), (p829,
  r464), (p856, r464), (p890, r464), (p205, r465), (p452, r465), (p593, r465), (p758, r465),
  (p776, r465), (p852, r465), (p275, r466), (p415, r466), (p425, r466), (p582, r466), (p652,
  r466), (p974, r466), (p263, r467), (p363, r467), (p397, r467), (p560, r467), (p569, r467),
  (p582, r467), (p761, r467), (p773, r467), (p825, r467), (p899, r467), (p923, r467)]

@[expose]
def deductions067 : List (Fin 990 × List (Fin 4)) :=
  [(p937, r467), (p217, r468), (p462, r468), (p490, r468), (p563, r468), (p578, r468), (p719,
  r468), (p848, r468), (p863, r468), (p890, r468), (p310, r469), (p322, r469), (p448, r469),
  (p449, r469), (p499, r469), (p608, r469), (p698, r469), (p880, r469), (p976, r469), (p250,
  r470), (p392, r470), (p428, r470), (p439, r470), (p499, r470), (p544, r470), (p677, r470),
  (p722, r470), (p851, r470), (p928, r470), (p936, r470), (p948, r470), (p212, r471)]

@[expose]
def deductions068 : List (Fin 990 × List (Fin 4)) :=
  [(p350, r471), (p628, r471), (p689, r471), (p720, r471), (p740, r471), (p763, r471), (p806,
  r471), (p238, r472), (p249, r472), (p381, r472), (p455, r472), (p461, r472), (p618, r472),
  (p650, r472), (p681, r472), (p889, r472), (p534, r473), (p557, r473), (p617, r473), (p701,
  r473), (p805, r473), (p932, r473), (p959, r473), (p981, r473), (p982, r473), (p99, r474),
  (p297, r474), (p376, r474), (p409, r474), (p497, r474), (p516, r474), (p529, r474)]

@[expose]
def deductions069 : List (Fin 990 × List (Fin 4)) :=
  [(p536, r474), (p554, r474), (p578, r474), (p690, r474), (p709, r474), (p718, r474), (p731,
  r474), (p740, r474), (p797, r474), (p805, r474), (p892, r474), (p985, r474), (p422, r475),
  (p584, r475), (p638, r475), (p858, r475), (p481, r476), (p541, r476), (p565, r476), (p616,
  r476), (p632, r476), (p761, r476), (p138, r477), (p234, r477), (p300, r477), (p352, r477),
  (p473, r477), (p541, r477), (p565, r477), (p629, r477), (p642, r477), (p691, r477)]

@[expose]
def deductions070 : List (Fin 990 × List (Fin 4)) :=
  [(p745, r477), (p770, r477), (p780, r477), (p845, r477), (p846, r477), (p850, r477), (p383,
  r478), (p548, r478), (p840, r478), (p942, r478), (p451, r479), (p467, r479), (p583, r479),
  (p732, r479), (p949, r479), (p966, r479), (p438, r480), (p599, r480), (p650, r480), (p719,
  r480), (p875, r480), (p934, r480), (p963, r480), (p440, r481), (p491, r481), (p499, r481),
  (p502, r481), (p803, r481), (p900, r481), (p311, r482), (p578, r482), (p832, r482)]

@[expose]
def deductions071 : List (Fin 990 × List (Fin 4)) :=
  [(p916, r482), (p974, r482), (p418, r483), (p652, r483), (p738, r483), (p786, r483), (p863,
  r483), (p864, r483), (p898, r483), (p730, r484), (p745, r485), (p361, r486), (p729, r486),
  (p730, r486), (p722, r487), (p755, r487), (p836, r487), (p918, r487), (p929, r487), (p382,
  r488), (p414, r488), (p434, r488), (p454, r488), (p457, r488), (p489, r488), (p503, r488),
  (p546, r488), (p573, r488), (p595, r488), (p636, r488), (p651, r488), (p673, r488)]

@[expose]
def deductions072 : List (Fin 990 × List (Fin 4)) :=
  [(p703, r488), (p835, r488), (p904, r488), (p929, r488), (p944, r488), (p962, r488), (p966,
  r488), (p105, r489), (p109, r489), (p169, r489), (p256, r489), (p328, r489), (p383, r489),
  (p397, r489), (p439, r489), (p456, r489), (p485, r489), (p548, r489), (p581, r489), (p711,
  r489), (p722, r489), (p762, r489), (p769, r489), (p815, r489), (p840, r489), (p860, r489),
  (p945, r489), (p948, r489), (p969, r489), (p232, r490), (p281, r490), (p299, r490)]

@[expose]
def deductions073 : List (Fin 990 × List (Fin 4)) :=
  [(p364, r490), (p519, r490), (p521, r490), (p648, r490), (p676, r490), (p748, r490), (p749,
  r490), (p760, r490), (p766, r490), (p828, r490), (p831, r490), (p852, r490), (p899, r490),
  (p912, r490), (p261, r491), (p385, r491), (p447, r491), (p449, r491), (p539, r491), (p664,
  r491), (p702, r491), (p766, r491), (p768, r491), (p812, r491), (p820, r491), (p833, r491),
  (p834, r491), (p879, r491), (p973, r491), (p402, r492), (p502, r492), (p561, r492)]

@[expose]
def deductions074 : List (Fin 990 × List (Fin 4)) :=
  [(p600, r492), (p659, r492), (p706, r492), (p853, r492), (p893, r492), (p923, r492), (p987,
  r492), (p282, r493), (p540, r493), (p570, r493), (p613, r493), (p833, r493), (p862, r493),
  (p323, r494), (p371, r494), (p509, r494), (p518, r494), (p669, r494), (p683, r494), (p711,
  r494), (p742, r494), (p770, r494), (p773, r494), (p835, r494), (p925, r494), (p90, r495),
  (p183, r495), (p200, r495), (p236, r495), (p354, r495), (p376, r495), (p407, r495)]

@[expose]
def deductions075 : List (Fin 990 × List (Fin 4)) :=
  [(p441, r495), (p495, r495), (p504, r495), (p536, r495), (p570, r495), (p594, r495), (p600,
  r495), (p615, r495), (p698, r495), (p749, r495), (p757, r495), (p791, r495), (p807, r495),
  (p816, r495), (p824, r495), (p845, r495), (p847, r495), (p849, r495), (p856, r495), (p917,
  r495), (p943, r495), (p964, r495), (p532, r496), (p562, r496), (p668, r496), (p740, r496),
  (p764, r496), (p774, r496), (p830, r496), (p839, r496), (p844, r496), (p910, r496)]

@[expose]
def deductions076 : List (Fin 990 × List (Fin 4)) :=
  [(p941, r496), (p989, r496), (p353, r497), (p469, r497), (p509, r497), (p545, r497), (p612,
  r497), (p693, r497), (p737, r497), (p777, r497), (p785, r497), (p789, r497), (p858, r497),
  (p863, r497), (p881, r497), (p896, r497), (p922, r497), (p928, r497), (p938, r497), (p972,
  r497), (p647, r498), (p700, r498), (p762, r498), (p808, r498), (p862, r498), (p958, r498),
  (p962, r498), (p970, r498), (p384, r499), (p495, r499), (p594, r499), (p654, r499)]

@[expose]
def deductions077 : List (Fin 990 × List (Fin 4)) :=
  [(p710, r499), (p733, r499), (p761, r499), (p786, r499), (p877, r499), (p898, r499), (p300,
  r500), (p340, r500), (p360, r500), (p385, r500), (p603, r500), (p618, r500), (p702, r500),
  (p736, r500), (p796, r500), (p844, r500), (p871, r500), (p877, r500), (p888, r500), (p891,
  r500), (p894, r500), (p924, r500), (p522, r501), (p791, r501), (p861, r501), (p986, r501),
  (p214, r502), (p264, r502), (p318, r502), (p379, r502), (p409, r502), (p525, r502)]

@[expose]
def deductions078 : List (Fin 990 × List (Fin 4)) :=
  [(p533, r502), (p535, r502), (p572, r502), (p587, r502), (p593, r502), (p621, r502), (p662,
  r502), (p741, r502), (p748, r502), (p764, r502), (p776, r502), (p788, r502), (p789, r502),
  (p852, r502), (p876, r502), (p896, r502), (p947, r502), (p959, r502), (p274, r503), (p298,
  r503), (p323, r503), (p364, r503), (p449, r503), (p470, r503), (p524, r503), (p532, r503),
  (p735, r503), (p839, r503), (p879, r503), (p936, r503), (p255, r504), (p260, r504)]

@[expose]
def deductions079 : List (Fin 990 × List (Fin 4)) :=
  [(p393, r504), (p507, r504), (p674, r504), (p758, r504), (p822, r504), (p954, r504), (p984,
  r504), (p416, r505), (p428, r505), (p431, r505), (p544, r505), (p567, r505), (p638, r505),
  (p647, r505), (p702, r505), (p762, r505), (p768, r505), (p781, r505), (p823, r505), (p833,
  r505), (p915, r505), (p928, r505), (p954, r505), (p152, r506), (p226, r506), (p444, r506),
  (p446, r506), (p448, r506), (p476, r506), (p486, r506), (p546, r506), (p576, r506)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
