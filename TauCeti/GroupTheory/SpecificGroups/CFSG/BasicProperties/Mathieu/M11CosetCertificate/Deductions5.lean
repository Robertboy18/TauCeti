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
# M11 coset certificate: Deductions5

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def deductions080 : List (Fin 990 × List (Fin 4)) :=
  [(p657, r506), (p674, r506), (p835, r506), (p839, r506), (p920, r506), (p984, r506), (p261,
  r507), (p524, r507), (p532, r507), (p630, r507), (p643, r507), (p650, r507), (p712, r507),
  (p754, r507), (p830, r507), (p895, r507), (p901, r507), (p932, r507), (p952, r507), (p967,
  r507), (p446, r508), (p455, r508), (p476, r508), (p504, r508), (p562, r508), (p808, r508),
  (p865, r508), (p933, r508), (p968, r508), (p431, r509), (p537, r509), (p559, r509)]

@[expose]
def deductions081 : List (Fin 990 × List (Fin 4)) :=
  [(p588, r509), (p679, r509), (p771, r509), (p780, r509), (p786, r509), (p797, r509), (p837,
  r509), (p872, r509), (p359, r510), (p372, r510), (p506, r510), (p522, r510), (p539, r510),
  (p622, r510), (p656, r510), (p664, r510), (p725, r510), (p737, r510), (p812, r510), (p814,
  r510), (p818, r510), (p860, r510), (p892, r510), (p903, r510), (p911, r510), (p930, r510),
  (p935, r510), (p942, r510), (p963, r510), (p968, r510), (p526, r511), (p586, r511)]

@[expose]
def deductions082 : List (Fin 990 × List (Fin 4)) :=
  [(p627, r511), (p645, r511), (p808, r511), (p815, r511), (p817, r511), (p861, r511), (p865,
  r511), (p875, r511), (p910, r511), (p933, r511), (p954, r511), (p989, r511), (p312, r512),
  (p359, r512), (p482, r512), (p492, r512), (p495, r512), (p526, r512), (p571, r512), (p622,
  r512), (p655, r512), (p737, r512), (p749, r512), (p802, r512), (p803, r512), (p807, r512),
  (p843, r512), (p859, r512), (p872, r512), (p945, r512), (p961, r512), (p275, r513)]

@[expose]
def deductions083 : List (Fin 990 × List (Fin 4)) :=
  [(p497, r513), (p547, r513), (p577, r513), (p625, r513), (p680, r513), (p742, r513), (p802,
  r513), (p826, r513), (p881, r513), (p934, r513), (p978, r513), (p526, r514), (p609, r514),
  (p643, r514), (p656, r514), (p694, r514), (p733, r514), (p748, r514), (p760, r514), (p812,
  r514), (p824, r514), (p828, r514), (p868, r514), (p872, r514), (p873, r514), (p889, r514),
  (p925, r514), (p935, r514), (p939, r514), (p584, r515), (p597, r515), (p613, r515)]

@[expose]
def deductions084 : List (Fin 990 × List (Fin 4)) :=
  [(p699, r515), (p766, r515), (p782, r515), (p796, r515), (p844, r515), (p848, r515), (p874,
  r515), (p876, r515), (p878, r515), (p883, r515), (p886, r515), (p896, r515), (p902, r515),
  (p941, r515), (p958, r515), (p967, r515), (p983, r515), (p984, r515), (p987, r515), (p327,
  r516), (p450, r516), (p470, r516), (p500, r516), (p524, r516), (p575, r516), (p581, r516),
  (p585, r516), (p607, r516), (p736, r516), (p796, r516), (p800, r516), (p816, r516)]

@[expose]
def deductions085 : List (Fin 990 × List (Fin 4)) :=
  [(p826, r516), (p856, r516), (p868, r516), (p342, r517), (p372, r517), (p512, r517), (p592,
  r517), (p626, r517), (p654, r517), (p747, r517), (p751, r517), (p763, r517), (p777, r517),
  (p782, r517), (p864, r517), (p881, r517), (p888, r517), (p895, r517), (p911, r517), (p918,
  r517), (p938, r517), (p547, r518), (p828, r518), (p836, r518), (p922, r518), (p975, r518),
  (p986, r518), (p987, r518), (p473, r519), (p781, r519), (p893, r519), (p963, r519)]

@[expose]
def deductions086 : List (Fin 990 × List (Fin 4)) :=
  [(p312, r520), (p330, r520), (p446, r520), (p450, r520), (p530, r520), (p564, r520), (p566,
  r520), (p590, r520), (p591, r520), (p607, r520), (p609, r520), (p611, r520), (p638, r520),
  (p667, r520), (p714, r520), (p720, r520), (p739, r520), (p773, r520), (p781, r520), (p788,
  r520), (p807, r520), (p832, r520), (p838, r520), (p874, r520), (p882, r520), (p888, r520),
  (p902, r520), (p905, r520), (p907, r520), (p915, r520), (p918, r520), (p924, r520)]

@[expose]
def deductions087 : List (Fin 990 × List (Fin 4)) :=
  [(p956, r520), (p958, r520), (p978, r520), (p395, r521), (p624, r521), (p633, r521), (p707,
  r521), (p765, r521), (p810, r521), (p830, r521), (p914, r521), (p945, r521), (p948, r521),
  (p970, r521), (p416, r522), (p440, r522), (p445, r522), (p481, r522), (p537, r522), (p544,
  r522), (p708, r522), (p734, r522), (p866, r522), (p894, r522), (p914, r522), (p925, r522),
  (p983, r522), (p989, r522), (p430, r523), (p518, r523), (p538, r523), (p581, r523)]

@[expose]
def deductions088 : List (Fin 990 × List (Fin 4)) :=
  [(p690, r523), (p757, r523), (p772, r523), (p820, r523), (p827, r523), (p866, r523), (p901,
  r523), (p907, r523), (p910, r523), (p953, r523), (p259, r524), (p445, r524), (p475, r524),
  (p540, r524), (p566, r524), (p579, r524), (p651, r524), (p675, r524), (p747, r524), (p818,
  r524), (p920, r524), (p965, r524), (p261, r525), (p705, r525), (p822, r525), (p957, r525),
  (p259, r526), (p415, r526), (p502, r526), (p517, r526), (p651, r526), (p668, r526)]

@[expose]
def deductions089 : List (Fin 990 × List (Fin 4)) :=
  [(p675, r526), (p681, r526), (p706, r526), (p711, r526), (p779, r526), (p795, r526), (p842,
  r526), (p859, r526), (p868, r526), (p870, r526), (p880, r526), (p886, r526), (p897, r526),
  (p900, r526), (p940, r526), (p956, r526), (p965, r526), (p975, r526), (p977, r526), (p619,
  r527), (p649, r527), (p694, r527), (p701, r527), (p765, r527), (p777, r527), (p821, r527),
  (p822, r527), (p850, r527), (p867, r527), (p882, r527), (p893, r527), (p913, r527)]

@[expose]
def deductions090 : List (Fin 990 × List (Fin 4)) :=
  [(p922, r527), (p939, r527), (p981, r527), (p627, r528), (p980, r528), (p819, r529), (p969,
  r529), (p767, r530), (p988, r530), (p534, r531), (p655, r531), (p819, r531), (p843, r531),
  (p972, r531), (p974, r531), (p985, r531), (p259, r532), (p388, r532), (p441, r532), (p443,
  r532), (p460, r532), (p621, r532), (p665, r532), (p765, r532), (p772, r532), (p776, r532),
  (p802, r532), (p819, r532), (p820, r532), (p821, r532), (p823, r532), (p842, r532)]

@[expose]
def deductions091 : List (Fin 990 × List (Fin 4)) :=
  [(p864, r532), (p920, r532), (p940, r532), (p957, r532), (p975, r532), (p982, r532), (p988,
  r532), (p486, r533), (p626, r533), (p707, r533), (p763, r533), (p767, r533), (p867, r533),
  (p878, r533), (p900, r533), (p927, r533), (p980, r533), (p230, r534), (p586, r534), (p594,
  r534), (p633, r534), (p878, r534), (p897, r534), (p913, r534), (p914, r534), (p915, r534),
  (p921, r534), (p930, r534), (p933, r534), (p939, r534), (p980, r534), (p983, r534)]

@[expose]
def deductions092 : List (Fin 990 × List (Fin 4)) :=
  [(p985, r534), (p356, r535), (p567, r535), (p675, r535), (p708, r535), (p769, r535), (p899,
  r535), (p901, r535), (p935, r535), (p964, r535), (p967, r535), (p870, r536), (p884, r536),
  (p921, r537), (p818, r538), (p905, r538), (p607, r539), (p919, r539), (p957, r539), (p843,
  r540), (p894, r540), (p913, r540), (p921, r540), (p930, r540), (p973, r540), (p988, r541),
  (p986, r542)]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
