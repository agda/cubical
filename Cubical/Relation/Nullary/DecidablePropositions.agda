module Cubical.Relation.Nullary.DecidablePropositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

private
  variable
    ℓ ℓ'  : Level

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

isSetDecProp : isSet (DecProp ℓ)
isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropDec (P .snd)))

-- the following is an alternative formulation of decidable propositions
-- it separates the boolean value from more proof-relevant part
-- so it performs better when doing computation

isDecProp : Type ℓ → Type ℓ
isDecProp P = Σ[ t ∈ Bool ] P ≃ Bool→Type t

DecProp' : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp' ℓ = Σ[ P ∈ Type ℓ ] isDecProp P

-- properties of the alternative formulation

isDecProp→isProp : {P : Type ℓ} → isDecProp P → isProp P
isDecProp→isProp h = isOfHLevelRespectEquiv 1 (invEquiv (h .snd)) isPropBool→Type

isDecProp→Dec : {P : Type ℓ} → isDecProp P → Dec P
isDecProp→Dec h = EquivPresDec (invEquiv (h .snd)) DecBool→Type

isPropIsDecProp : {P : Type ℓ} → isProp (isDecProp P)
isPropIsDecProp p q =
  Σ≡PropEquiv (λ _ → isOfHLevel⁺≃ᵣ 0 isPropBool→Type) .fst
    (Bool→TypeInj _ _ (invEquiv (p .snd) ⋆ q .snd))

isDecPropRespectEquiv : {P : Type ℓ} {Q : Type ℓ'}
  → P ≃ Q → isDecProp Q → isDecProp P
isDecPropRespectEquiv e (t , e') = t , e ⋆ e'

DecProp→isFinOrd :
  ∀ {ℓ} → (A : DecProp ℓ) → isFinOrd (A .fst .fst)
DecProp→isFinOrd A =
  decRec
    (λ a →
      1 ,
      isoToEquiv
      (iso
        (λ _ → inl _)
        (λ { (inl tt) → a ; (inr ()) })
        (λ { (inl tt) → refl ; (inr ()) })
        (λ a → A .fst .snd _ _)))
    (λ ¬a → 0 , uninhabEquiv ¬a (λ x → x))
    (A .snd)
