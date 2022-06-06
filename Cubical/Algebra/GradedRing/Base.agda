{-# OPTIONS --safe #-}
module Cubical.Algebra.GradedRing.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.Algebra.GradedRing.DirectSumHIT

private variable
  ℓ ℓ' : Level

open AbGroupStr



record IsGradedRing (R    : Ring (ℓ-max ℓ ℓ'))
                    (IdM  : Monoid ℓ)
                    (G    : (k : (fst IdM)) → Type ℓ')
                    (Gstr : (k : fst IdM) → AbGroupStr (G k))
                    (1⋆   : G (MonoidStr.ε (snd IdM)))
                    (_⋆_  : {k l : fst IdM} → G k → G l → G (MonoidStr._·_ (snd IdM) k l))
                    : Type (ℓ-max ℓ ℓ')
                    where

  constructor isgradedring

  private
    Idx = fst IdM
    open MonoidStr (snd IdM)

  field
    0-⋆     : {k l : Idx} → (b : G l) → (0g (Gstr k)) ⋆ b ≡ 0g (Gstr (k · l))
    ⋆-0     : {k l : Idx} → (a : G k) → a ⋆ (0g (Gstr l)) ≡ 0g (Gstr (k · l))
    ⋆Assoc  : {k l m : Idx} → (a : G k) → (b : G l) → (c : G m) →
               _≡_ {A = Σ[ k ∈ Idx ] G k} ((k · (l · m)) , (a ⋆ (b ⋆ c))) (((k · l) · m) , ((a ⋆ b) ⋆ c))
    ⋆IdR    : {k : Idx} → (a : G k) → _≡_ {A = Σ[ k ∈ Idx ] G k} ( k · ε , a ⋆ 1⋆ ) (k , a)
    ⋆IdL    : {l : Idx} → (b : G l) → _≡_ {A = Σ[ k ∈ Idx ] G k} ( ε · l , 1⋆ ⋆ b ) (l , b)
    ⋆DistR+ : {k l : Idx} → (a : G k) → (b c : G l) →
              a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (k · l) ._+_ (a ⋆ b) (a ⋆ c)
    ⋆DistL+ : {k l : Idx} → (a b : G k) → (c : G l) →
              ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (k · l) ._+_ (a ⋆ c) (b ⋆ c)
    equivRing : RingEquiv R (⊕HITgradedRing-Ring IdM G Gstr 1⋆ _⋆_
                                                 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+)


record GradedRingStr (R : Ring (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor gradedringstr

  field
    IdM : Monoid ℓ
    G : (k : (fst IdM)) → Type ℓ'
    Gstr : (k : fst IdM) → AbGroupStr (G k)
    1⋆ : G (MonoidStr.ε (snd IdM))
    _⋆_ : {k l : fst IdM} → G k → G l → G (MonoidStr._·_ (snd IdM) k l)
    isGradedRing : IsGradedRing R IdM G Gstr 1⋆ _⋆_
