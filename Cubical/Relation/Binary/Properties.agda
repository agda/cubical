{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ


-- Pulling back a relation along a function.
-- This can for example be used when restricting an equivalence relation to a subset:
--   _~'_ = on fst _~_

module _
  (f : A → B)
  (R : Rel B B ℓ)
  where

  open BinaryRelation

  pulledbackRel : Rel A A ℓ
  pulledbackRel x y = R (f x) (f y)

  isReflPulledbackRel : isRefl R → isRefl pulledbackRel
  isReflPulledbackRel isReflR a = isReflR (f a)

  isSymPulledbackRel : isSym R → isSym pulledbackRel
  isSymPulledbackRel isSymR a a' = isSymR (f a) (f a')

  isTransPulledbackRel : isTrans R → isTrans pulledbackRel
  isTransPulledbackRel isTransR a a' a'' = isTransR (f a) (f a') (f a'')

  open isEquivRel

  isEquivRelPulledbackRel : isEquivRel R → isEquivRel pulledbackRel
  reflexive (isEquivRelPulledbackRel isEquivRelR) = isReflPulledbackRel (reflexive isEquivRelR)
  symmetric (isEquivRelPulledbackRel isEquivRelR) = isSymPulledbackRel (symmetric isEquivRelR)
  transitive (isEquivRelPulledbackRel isEquivRelR) = isTransPulledbackRel (transitive isEquivRelR)

module _ {A B : Type ℓ} (e : A ≃ B) {_∼_ : Rel A A ℓ'} {_∻_ : Rel B B ℓ'}
         (_h_ : ∀ x y → (x ∼ y) ≃ ((fst e x) ∻ (fst e y))) where

  RelPathP : PathP (λ i → ua e i → ua e i → Type _)
              _∼_ _∻_
  RelPathP i x y = Glue  (ua-unglue e i x ∻ ua-unglue e i y)
      λ { (i = i0) → _ ,  x h y
        ; (i = i1) → _ , idEquiv _ }


module _ {ℓ''} {B : Type ℓ} {_∻_ : B → B → Type ℓ'} where

  JRelPathP-Goal : Type _
  JRelPathP-Goal = ∀ (A : Type ℓ) (e : A ≃ B) (_~_ : A → A → Type ℓ')
             → (_h_ :  ∀ x y → x ~ y ≃ (fst e x ∻ fst e  y)) → Type ℓ''


  EquivJRel : (Goal : JRelPathP-Goal)
            → (Goal _ (idEquiv _) _∻_ λ _ _ → idEquiv _ )
            → ∀ {A} e _~_ _h_ → Goal A e _~_ _h_
  EquivJRel Goal g {A} = EquivJ (λ A e → ∀ _~_ _h_ → Goal A e _~_ _h_)
   λ _~_ _h_ → subst (uncurry (Goal B (idEquiv B)))
       ((isPropRetract
           (map-snd (λ r → funExt₂ λ x y → sym (ua (r x y))))
           (map-snd (λ r x y → pathToEquiv λ i → r (~ i) x y))
           (λ (o , r) → cong (o ,_) (funExt₂ λ x y → equivEq
              (funExt λ _ → transportRefl _)))
          (isPropSingl {a = _∻_})) _ _) g
