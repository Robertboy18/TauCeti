/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions5

/-!
# M11 coset certificate: Deductions

Ordered pairs of a table point and a scan or subgroup word.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

/-- The 2971 deductions, concatenated in their original order. -/
@[expose]
def deductions : List (Fin 990 × List (Fin 4)) :=
  List.append deductions000 <|
  List.append deductions001 <|
  List.append deductions002 <|
  List.append deductions003 <|
  List.append deductions004 <|
  List.append deductions005 <|
  List.append deductions006 <|
  List.append deductions007 <|
  List.append deductions008 <|
  List.append deductions009 <|
  List.append deductions010 <|
  List.append deductions011 <|
  List.append deductions012 <|
  List.append deductions013 <|
  List.append deductions014 <|
  List.append deductions015 <|
  List.append deductions016 <|
  List.append deductions017 <|
  List.append deductions018 <|
  List.append deductions019 <|
  List.append deductions020 <|
  List.append deductions021 <|
  List.append deductions022 <|
  List.append deductions023 <|
  List.append deductions024 <|
  List.append deductions025 <|
  List.append deductions026 <|
  List.append deductions027 <|
  List.append deductions028 <|
  List.append deductions029 <|
  List.append deductions030 <|
  List.append deductions031 <|
  List.append deductions032 <|
  List.append deductions033 <|
  List.append deductions034 <|
  List.append deductions035 <|
  List.append deductions036 <|
  List.append deductions037 <|
  List.append deductions038 <|
  List.append deductions039 <|
  List.append deductions040 <|
  List.append deductions041 <|
  List.append deductions042 <|
  List.append deductions043 <|
  List.append deductions044 <|
  List.append deductions045 <|
  List.append deductions046 <|
  List.append deductions047 <|
  List.append deductions048 <|
  List.append deductions049 <|
  List.append deductions050 <|
  List.append deductions051 <|
  List.append deductions052 <|
  List.append deductions053 <|
  List.append deductions054 <|
  List.append deductions055 <|
  List.append deductions056 <|
  List.append deductions057 <|
  List.append deductions058 <|
  List.append deductions059 <|
  List.append deductions060 <|
  List.append deductions061 <|
  List.append deductions062 <|
  List.append deductions063 <|
  List.append deductions064 <|
  List.append deductions065 <|
  List.append deductions066 <|
  List.append deductions067 <|
  List.append deductions068 <|
  List.append deductions069 <|
  List.append deductions070 <|
  List.append deductions071 <|
  List.append deductions072 <|
  List.append deductions073 <|
  List.append deductions074 <|
  List.append deductions075 <|
  List.append deductions076 <|
  List.append deductions077 <|
  List.append deductions078 <|
  List.append deductions079 <|
  List.append deductions080 <|
  List.append deductions081 <|
  List.append deductions082 <|
  List.append deductions083 <|
  List.append deductions084 <|
  List.append deductions085 <|
  List.append deductions086 <|
  List.append deductions087 <|
  List.append deductions088 <|
  List.append deductions089 <|
  List.append deductions090 <|
  List.append deductions091 <|
  deductions092

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
