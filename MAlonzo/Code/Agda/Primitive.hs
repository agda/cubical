{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Agda.Primitive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name14 = "Agda.Primitive.Level"
type T14 = ()
d14
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Primitive.Level"
name16 = "Agda.Primitive.lzero"
d16 = ()
name20 = "Agda.Primitive.lsuc"
d20 = (\ _ -> ())
name26 = "Agda.Primitive._⊔_"
d26 = (\ _ _ -> ())
