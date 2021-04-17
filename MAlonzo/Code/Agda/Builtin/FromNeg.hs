{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Agda.Builtin.FromNeg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name10 = "Agda.Builtin.FromNeg.Negative"
d10 a0 a1 = ()
newtype T10 = C17 (Integer -> AgdaAny -> AgdaAny)
name24 = "Agda.Builtin.FromNeg.Negative.Constraint"
d24 :: T10 -> Integer -> ()
d24 = erased
name30 = "Agda.Builtin.FromNeg.Negative.fromNeg"
d30 :: T10 -> Integer -> AgdaAny -> AgdaAny
d30 v0
  = case coe v0 of
      C17 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name34 = "Agda.Builtin.FromNeg._.fromNeg"
d34 :: T10 -> Integer -> AgdaAny -> AgdaAny
d34 v0 = coe d30 (coe v0)
