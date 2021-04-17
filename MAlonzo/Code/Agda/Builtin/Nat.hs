{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Agda.Builtin.Nat where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name6 = "Agda.Builtin.Nat.Nat"
d6 = ()
data T6 = C8 | C12 Integer
name14 = "Agda.Builtin.Nat._+_"
d14 = ((+) :: Integer -> Integer -> Integer)
name22 = "Agda.Builtin.Nat._-_"
d22 = ((\ x y -> max 0 (x - y)) :: Integer -> Integer -> Integer)
name32 = "Agda.Builtin.Nat._*_"
d32 = ((*) :: Integer -> Integer -> Integer)
name40 = "Agda.Builtin.Nat._==_"
d40 = ((==) :: Integer -> Integer -> Bool)
name46 = "Agda.Builtin.Nat._<_"
d46 = ((<) :: Integer -> Integer -> Bool)
name60 = "Agda.Builtin.Nat.div-helper"
d60
  = ((\ k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Integer -> Integer -> Integer -> Integer -> Integer)
name90 = "Agda.Builtin.Nat.mod-helper"
d90
  = ((\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n)) :: Integer -> Integer -> Integer -> Integer -> Integer)
