{-

This module defines a 'Setoid' as a pair consisting of an hSet and a propositional equivalence relation over it.

In contrast to the standard Agda library where setoids act as carriers for different algebraic structures, this usage is not relevant in cubical-agda context due to the availability of set quotients.

The Setoids from this module are given categorical structure in Cubical.Categories.Instances.Setoids.

-}


{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Setoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Properties
open import Cubical.Data.Sigma

private
  variable
    ℓX ℓX' ℓA ℓ≅A ℓA' ℓ≅A' : Level
    A : Type ℓA
    A' : Type ℓA'

Setoid : ∀ ℓA ℓ≅A → Type (ℓ-suc (ℓ-max ℓA ℓ≅A))
Setoid ℓA ℓ≅A = Σ (hSet ℓA) λ (X , _) → EquivPropRel X ℓ≅A

SetoidMor : (Setoid ℓA ℓ≅A) → (Setoid ℓA' ℓ≅A') → Type _
SetoidMor (_ , ((R , _) , _)) (_ , ((R' , _) , _)) = Σ _ (respects R R')

isSetSetoidMor :
 {A : Setoid ℓA ℓ≅A}
 {A' : Setoid ℓA' ℓ≅A'}
 → isSet (SetoidMor A A')
isSetSetoidMor {A' = (_ , isSetB) , ((_ , isPropR) , _)} =
 isSetΣ (isSet→ isSetB) (isProp→isSet ∘ isPropRespects isPropR )

SetoidMor≡ : ∀ A A' → {f g : SetoidMor {ℓA = ℓA} {ℓ≅A} {ℓA'} {ℓ≅A'} A A'}
              → fst f ≡ fst g → f ≡ g
SetoidMor≡ _ ((_ , (_ , pr) , _)) = Σ≡Prop (isPropRespects pr)

substRel : ∀ {x y : A'} → {f g : A' → A} → (R : Rel A A ℓ≅A)
              → (∀ x → f x ≡ g x) →
               R (f x) (f y) → R (g x) (g y)
substRel R p = subst2 R (p _) (p _)

_⊗_ : (Setoid ℓA ℓ≅A) → (Setoid ℓA' ℓ≅A')
      → Setoid (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A')
((_ , isSetA) , ((_ , pr) , eqr)) ⊗ ((_ , isSetA') , ((_ , pr') , eqr')) =
  (_ , isSet× isSetA isSetA')
   , (_ , λ _ _ → isProp× (pr _ _) (pr' _ _)) ,
        isEquivRel×Rel eqr eqr'

_⟶_ : (Setoid ℓA ℓ≅A) → (Setoid ℓA' ℓ≅A') → Setoid _ _
A@((⟨A⟩ , _) , ((R , _) , _)) ⟶ A'@(_ , ((_ , pr) , eqr)) =
  (_ , isSetSetoidMor {A = A} {A'}) ,
  (_ , λ _ _ → isPropΠ λ _ → pr _ _) ,
  isEquivRelPulledbackRel (isEquivRelFunRel eqr {A = ⟨A⟩}) fst

open Iso

setoidCurryIso :
   (X : Setoid ℓX ℓX') (A : Setoid ℓA ℓ≅A) (B : Setoid ℓA' ℓ≅A')
 → Iso (SetoidMor (A ⊗ X) B)
       (SetoidMor A (X ⟶ B))
fun (setoidCurryIso (_ , (_ , Rx)) (_ , (_ , Ra)) _ ) (f , p) =
 (λ _ → curry f _ , p {_ , _} {_ , _} ∘ (reflexive Ra _ ,_)) ,
  flip λ _ → p {_ , _} {_ , _} ∘ (_, reflexive Rx _)
 where open BinaryRelation.isEquivRel
inv (setoidCurryIso X _ (_ , (_ , Rb))) (f , p) = (uncurry (fst ∘ f))
 , λ (a~a' , b~b') → transitive' (p a~a' _)  (snd (f _) b~b')
  where open BinaryRelation.isEquivRel Rb using (transitive')
rightInv (setoidCurryIso X A B) _ =
  SetoidMor≡ A (X ⟶ B) (funExt λ _ → SetoidMor≡ X B refl)
leftInv (setoidCurryIso X A B) _ = SetoidMor≡ (A ⊗ X) B refl
