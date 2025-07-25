module Cubical.Algebra.Group.DirProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open GroupStr
open IsGroup hiding (·IdR ; ·IdL ; ·InvR ; ·InvL)
open IsMonoid hiding (·IdR ; ·IdL)
open IsSemigroup

DirProd : ∀ {ℓ ℓ'} → Group ℓ → Group ℓ' → Group (ℓ-max ℓ ℓ')
fst (DirProd G H) = (fst G) × (fst H)
1g (snd (DirProd G H)) = (1g (snd G)) , (1g (snd H))
_·_ (snd (DirProd G H)) (g , h) (g' , h') = _·_ (snd G) g g' , _·_ (snd H) h h'
inv (snd (DirProd G H)) (g , h) = (inv (snd G) g) , (inv (snd H) h)
isGroup (snd (DirProd G H)) = makeIsGroup
                              (isSet× (is-set (snd G)) (is-set (snd H)))
                              (λ x y z → ≡-× (·Assoc (snd G) _ _ _) (·Assoc (snd H) _ _ _))
                              (λ x → ≡-× (·IdR (snd G) _) (·IdR (snd H) _))
                              (λ x → ≡-× (·IdL (snd G) _) (·IdL (snd H) _))
                              (λ x → ≡-× (·InvR (snd G) _) (·InvR (snd H) _))
                              λ x → ≡-× (·InvL (snd G) _) (·InvL (snd H) _)
