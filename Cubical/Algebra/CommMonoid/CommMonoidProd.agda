{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.CommMonoidProd where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.Base


open CommMonoidStr
open IsCommMonoid hiding (rid ; lid)
open IsMonoid hiding (rid ; lid)
open IsSemigroup


private
  variable
    ℓ ℓ' : Level


CommMonoidProd : CommMonoid ℓ → CommMonoid ℓ' → CommMonoid (ℓ-max ℓ ℓ')
CommMonoidProd M N = makeCommMonoid ε× _·×_ is-set× assoc× rid× comm×
  where
  ε× : (fst M) × (fst N)
  ε× = (ε (snd M)) , (ε (snd N))

  _·×_ : (fst M) × (fst N) → (fst M) × (fst N) → (fst M) × (fst N)
  (x₁ , x₂) ·× (y₁ , y₂) = (_·_ (snd M) x₁ y₁) , (_·_ (snd N) x₂ y₂)

  is-set× : isSet ((fst M) × (fst N))
  is-set× = isSet× (is-set (snd M)) (is-set (snd N))

  assoc× : ∀ x y z → x ·× (y ·× z) ≡ (x ·× y) ·× z
  assoc× _ _ _ = cong₂ (_,_) (assoc (snd M) _ _ _) (assoc (snd N) _ _ _)

  rid× : ∀ x → x ·× ε× ≡ x
  rid× _ =  cong₂ (_,_) (rid (snd M) _) (rid (snd N) _)

  comm× : ∀ x y → x ·× y ≡ y ·× x
  comm× _ _ = cong₂ (_,_) (comm (snd M) _ _) (comm (snd N) _ _)
