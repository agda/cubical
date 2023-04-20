{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.DirProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
import Cubical.Algebra.Group.DirProd as Group
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group.Morphisms

private variable
  ℓ ℓ' : Level

open AbGroupStr

DirProd : AbGroup ℓ → AbGroup ℓ' → AbGroup (ℓ-max ℓ ℓ')
DirProd A B =
  Group→AbGroup (Group.DirProd (AbGroup→Group A) (AbGroup→Group B))
                 λ p q → ΣPathP (+Comm (snd A) _ _ , +Comm (snd B) _ _)


open Iso

-- A coherence
DirProdForgetComm : ∀ {ℓ ℓ'} → (G : AbGroup ℓ) → (H : AbGroup ℓ')
                    → GroupIso (AbGroup→Group (DirProd G H)) (Group.DirProd (AbGroup→Group G) (AbGroup→Group H))
fun (fst (DirProdForgetComm G H)) = λ x → x
inv (fst (DirProdForgetComm G H)) = λ x → x
rightInv (fst (DirProdForgetComm G H)) x = refl
leftInv (fst (DirProdForgetComm G H)) x = refl
snd (DirProdForgetComm G H) = record { pres· = λ _ _ → refl ; pres1 = refl ; presinv = λ x → refl }
