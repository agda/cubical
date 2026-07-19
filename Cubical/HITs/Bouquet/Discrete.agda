
{-

This module, uses normalization and decidable equality from `Cubical.Algebra.Group.Free` to demonstrate that Bouquet over discrete type is hGroupoid by establishing a coding between loops in the bouquet and elements of the FreeGroup represented by normalised words.

-}

module Cubical.HITs.Bouquet.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (rec to recList)
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary


open import Cubical.HITs.Bouquet.Base
open import Cubical.Algebra.Group.Free


private
  variable
    ℓ : Level

module _ {A : Type ℓ} (_≟_ : Discrete A) where

  open NormalForm A

  open Discrete _≟_


  CodeBouquet : Bouquet A → Type ℓ
  CodeBouquet base = Σ _ IsNormalised
  CodeBouquet (loop a i) = ua (η·≃ (true , a)) i

  co→ : ∀ x → base ≡ x → CodeBouquet x
  co→ x p = subst CodeBouquet p ([] , lower)

  co←base-step : Bool × A → Path (Bouquet A) base base

  co←base-step (b , a) = if b then (idfun _) else sym $ loop a

  co←base : [𝟚× A ] → Path (Bouquet A) base base
  co←base = recList refl (flip _∙_ ∘ co←base-step)

  co← : ∀ x → CodeBouquet x → base ≡ x
  co← base = co←base ∘ fst
  co← (loop a i) x j = co←Sq a i j x
   where

   co←Sq : (a : A) → SquareP (λ i j →  ua (η·≃ (true , a)) i → Bouquet A)
                        (funExt (co←base ∘ fst))
                        (funExt (co←base ∘ fst))
                        (λ _ _ → base)
                        (λ i _ → loop a i)
   co←Sq a = congP (λ _ → funExt) (ua→ (uncurry
      (λ xs y → co←Sq' a xs y (HeadIsRedex? ((true , a) ∷ xs)))))
    where
    co←Sq' : (a : A) → (x : [𝟚× A ]) (y : IsNormalised x) →
       ∀ u → PathP (λ i → base ≡ loop a i)
       (recList (λ _ → base) (flip _∙_ ∘ co←base-step) x)
       (recList (λ _ → base) (flip _∙_ ∘ co←base-step) (preη· (true , a) x u ))
    co←Sq' a ((false , snd₁) ∷ xs) y (yes p) =
      cong (λ x' → co←base ((false , x') ∷ xs)) (cong snd (sym p))
        ◁ symP (compPath-filler (co←base xs) (sym (loop a)))
    co←Sq' a xs y (no ¬p) = compPath-filler _ _
    co←Sq' a ((true , snd₁) ∷ xs) y (yes p) = ⊥.rec (true≢false (cong fst p))

  coSec : ∀ x → section (co← x) (co→ x)
  coSec _ = J (λ x b → co← x (co→ x b) ≡ b) refl

  coRet : (x : [𝟚× A ]) (y : IsNormalised x) →
            fst (subst CodeBouquet (co← base (x , y)) ([] , lower))
                  ≡ x
  coRet [] y = refl
  coRet (x@(b , a) ∷ xs) y =
    cong fst (substComposite CodeBouquet (co← base (xs , y ∘ inr))
      (co←base-step x) _)
      ∙∙
      cong (fst ∘ subst CodeBouquet (co←base-step x))
         (Σ≡Prop isPropIsNormalised (coRet xs (y ∘ inr))) ∙∙
      lem b xs (y ∘ inr) ∙ η·∷ x xs (y ∘ inl)

   where
   lem : ∀ b xs y → fst
      (subst CodeBouquet (co←base-step (b , a)) (xs , y))
      ≡ η· (b , a) xs
   lem false xs y = cong fst (~uaβ (η·≃ (true , a)) (xs , y ))
   lem true xs y = cong fst (uaβ (η·≃ (true , a)) (xs , y ))


  codeDecode : Iso (Path (Bouquet A) base base)
                   (Σ _ IsNormalised)
  Iso.fun codeDecode p = subst CodeBouquet p ([] , lower)
  Iso.inv codeDecode = co← base
  Iso.rightInv codeDecode = Σ≡Prop isPropIsNormalised ∘ uncurry coRet
  Iso.leftInv codeDecode = coSec base

  isSetΩBouquet : isSet (Path (Bouquet A) base base)
  isSetΩBouquet = isOfHLevelRetractFromIso 2 codeDecode
                     (isSetΣ isSet[𝟚×] (isProp→isSet ∘ isPropIsNormalised))

  isGroupoidBouquet : isGroupoid (Bouquet A)
  isGroupoidBouquet base base = isSetΩBouquet
  isGroupoidBouquet base (loop x i) = isProp→PathP
   (λ i → isPropIsSet {A = Path (Bouquet A) base (loop x i)}) isSetΩBouquet isSetΩBouquet i
  isGroupoidBouquet (loop x i) base = isProp→PathP
   (λ i → isPropIsSet {A = Path (Bouquet A) (loop x i) base}) isSetΩBouquet isSetΩBouquet i
  isGroupoidBouquet (loop x i) (loop x₁ i₁) = isSet→SquareP
      (λ i i₁ → isProp→isSet (isPropIsSet {A = Path (Bouquet A) (loop x i) (loop x₁ i₁)}))
      (isProp→PathP
         (λ i → isPropIsSet {A = Path (Bouquet A) base (loop x₁ i)}) isSetΩBouquet isSetΩBouquet)
      (isProp→PathP
         (λ i → isPropIsSet {A = Path (Bouquet A) base (loop x₁ i)}) isSetΩBouquet isSetΩBouquet)
      (isProp→PathP
         (λ i → isPropIsSet {A = Path (Bouquet A) (loop x i) base}) isSetΩBouquet isSetΩBouquet)
      (isProp→PathP
         (λ i → isPropIsSet {A = Path (Bouquet A) (loop x i) base}) isSetΩBouquet isSetΩBouquet)
     i i₁
