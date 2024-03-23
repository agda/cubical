{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.DirectProduct where

open import Cubical.Data.Sigma
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.DirProd

AbDirProd : ∀ {ℓ ℓ'} → AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')
AbDirProd G H =
  Group→AbGroup (DirProd (AbGroup→Group G) (AbGroup→Group H)) comm
  where
  comm : (x y : fst G × fst H) → _ ≡ _
  comm (g1 , h1) (g2 , h2) =
    ΣPathP (AbGroupStr.+Comm (snd G) g1 g2
          , AbGroupStr.+Comm (snd H) h1 h2)
