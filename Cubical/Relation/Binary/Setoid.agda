{-

This module defines a 'Setoid' as a pair consisting of an hSet and a propositional equivalence relation over it.

In contrast to the standard Agda library where setoids act as carriers for different algebraic structures, this usage is not relevant in cubical-agda context due to the availability of set quotients.

The Setoids from this module are given categorical structure in Cubical.Categories.Instances.Setoids.

-}


{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Setoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓX ℓX' ℓA ℓ≅A ℓA' ℓ≅A' : Level
    A : Type ℓA
    A' : Type ℓA'

Setoid : ∀ ℓA ℓ≅A → Type (ℓ-suc (ℓ-max ℓA ℓ≅A))
Setoid ℓA ℓ≅A = Σ (hSet ℓA) λ (X , _) → EquivPropRel X ℓ≅A

Setoid≡ : (A@((A' , _) , ((_∼_ , _) , _)) B@((B' , _) , ((_∻_ , _) , _)) : Setoid ℓA ℓ≅A) →
              (e : A' ≃ B')
              → (∀ x y → (x ∼ y) ≃ ((fst e x) ∻ (fst e y))) → A ≡ B
Setoid≡ A B e x =
  ΣPathP (TypeOfHLevel≡ 2 (ua e) ,
          ΣPathPProp ( BinaryRelation.isPropIsEquivPropRel _ ∘ snd)
             (ΣPathPProp (λ _ → isPropΠ2 λ _ _ → isPropIsProp) (RelPathP _ x)))

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

setoidUnit : Setoid ℓX ℓX'
setoidUnit = (Unit* , isSetUnit*) , fullEquivPropRel

hPropSetoid : ∀ ℓ → Setoid (ℓ-suc ℓ) ℓ
fst (hPropSetoid ℓ) = _ , isSetHProp {ℓ}
fst (fst (snd (hPropSetoid ℓ))) = _
snd (fst (snd (hPropSetoid ℓ))) a b = snd (a ⇔ b)
snd (snd (hPropSetoid ℓ)) =
 BinaryRelation.equivRel
  (λ _ → idfun _ , idfun _)
  (λ _ _ (x , y) → y , x)
  λ _ _ _ (f , g') (f' , g) → f' ∘ f , g' ∘ g

Strengthen : (A : Setoid ℓA ℓA') → EquivPropRel (fst (fst A)) ℓX → Setoid ℓA (ℓ-max ℓA' ℓX)
Strengthen A x = fst A , (_ , λ _ _ → isProp× (snd (fst (snd A)) _ _) (snd (fst x) _ _))
                    , isEquivRel⊓Rel (snd (snd A)) (snd x)

SetoidΣ : (A : Setoid ℓA ℓA') → (B : Setoid ℓX ℓX') → SetoidMor A B
            → Setoid ℓA (ℓ-max ℓA' ℓX') 
SetoidΣ A B f = Strengthen A ((_ , λ _ _ → snd (fst (snd B)) _ _) ,
   isEquivRelPulledbackRel (snd (snd B)) (fst f))

setoidΣ-pr₁ : (A : Setoid ℓA ℓA') → (B : Setoid ℓX ℓX')
            → (f : SetoidMor A B) 
            → SetoidMor (SetoidΣ A B f) B            
setoidΣ-pr₁ A B f = _ , snd f ∘ fst


module _ (𝑨@((A , isSetA) , ((_∼_ , propRel∼) , eqRel∼)) : Setoid ℓA ℓA')
         (P :  A → hProp ℓX) where

 ΣPropSetoid : Setoid (ℓ-max ℓA ℓX) ℓA' 
 fst (fst ΣPropSetoid) = Σ A (fst ∘ P)
 snd (fst ΣPropSetoid) = isSetΣ isSetA (isProp→isSet ∘ snd ∘ P)
 fst (snd ΣPropSetoid) = _ , λ _ _ → propRel∼ _ _
 snd (snd ΣPropSetoid) = isEquivRelPulledbackRel eqRel∼ fst

setoidSection : (A : Setoid ℓA ℓA') → (B : Setoid ℓX ℓX') → SetoidMor A B
            → Setoid _ _
setoidSection A B (_ , f) = ΣPropSetoid (B ⟶ A)
  λ (_ , g) → _ , snd (fst (snd (B ⟶ B))) (_ , f ∘ g  ) (_ , idfun _)

-- setoidΠ-pr₁ : (A : Setoid ℓA ℓA') → (B : Setoid ℓX ℓX')
--             → (f : SetoidMor A B) 
--             → SetoidMor (setoidSection A B f) B            
-- setoidΠ-pr₁ A B f = {!!}


-- module _ (𝑨@((A , isSetA) , ((_∼_ , propRel∼) , eqRel∼)) : Setoid ℓA ℓA')
--          ((P , Presp) : SetoidMor 𝑨 (hPropSetoid ℓX)) where

--  ΣPropSetoid : Setoid (ℓ-max ℓA ℓX) ℓA' 
--  fst (fst ΣPropSetoid) = Σ A (fst ∘ P)
--  snd (fst ΣPropSetoid) = isSetΣ isSetA (isProp→isSet ∘ snd ∘ P)
--  fst (snd ΣPropSetoid) = _ , λ _ _ → propRel∼ _ _
--  snd (snd ΣPropSetoid) = isEquivRelPulledbackRel eqRel∼ fst


module _ (L R M : Setoid ℓA ℓA') (s₁ : SetoidMor L M) (s₂ : SetoidMor R M) where

 PullbackSetoid : Setoid ℓA ℓA'
 PullbackSetoid =
   (Σ (fst (fst L) × fst (fst R)) (λ (l , r) → fst s₁ l ≡ fst s₂ r) ,
      isSetΣ (isSet× (snd (fst L)) (snd (fst R))) (λ _ → isProp→isSet (snd (fst M) _ _))) ,
    (_ , λ _ _ → (isProp× (snd (fst (snd L)) _ _ ) (snd (fst (snd R)) _ _))) ,
    
     (isEquivRelPulledbackRel (isEquivRel×Rel (snd (snd L)) (snd (snd R))) fst)
    
  where open BinaryRelation.isEquivRel (snd (snd M)) renaming (transitive' to _⊚_)

module _ (L R M : Setoid ℓA ℓA') (s₁ : SetoidMor L M) (s₂ : SetoidMor R M) where

 EPullbackSetoid : Setoid (ℓ-max ℓA ℓA') ℓA'
 EPullbackSetoid =
   (Σ (fst (fst L) × fst (fst R)) (λ (l , r) → fst (fst (snd M)) (fst s₁ l) (fst s₂ r)) ,
      isSetΣ (isSet× (snd (fst L)) (snd (fst R))) (λ _ → isProp→isSet (snd (fst (snd M)) _ _))) ,
    
    (_ , λ _ _ → isProp× (snd (fst (snd L)) _ _ ) (snd (fst (snd R)) _ _)) ,
     isEquivRelPulledbackRel (isEquivRel×Rel (snd (snd L)) (snd (snd R))) fst


 -- EPullbackSetoid₂ : Setoid (ℓ-max ℓA ℓA') ℓA'
 -- EPullbackSetoid₂ =
 --   (Σ (fst (fst L) × fst (fst R)) (λ (l , r) → fst (fst (snd M)) (fst s₁ l) (fst s₂ r)) ,
 --      isSetΣ (isSet× (snd (fst L)) (snd (fst R))) (λ _ → isProp→isSet (snd (fst (snd M)) _ _))) ,
    
 --    (_ , λ _ _ → isProp× (isProp× (snd (fst (snd L)) _ _ ) (snd (fst (snd R)) _ _))
 --      (snd (fst (snd M)) _ _)) ,
       
 --    isEquivRel⊓Rel
 --     (isEquivRelPulledbackRel (isEquivRel×Rel (snd (snd L)) (snd (snd R))) fst)
 --     (isEquivRelPulledbackRel (snd (snd M)) λ x → fst s₂ (snd (fst x)))

 -- EPullbackSetoid₁₌₂ : EPullbackSetoid₁ ≡ EPullbackSetoid₂
 -- EPullbackSetoid₁₌₂ = Setoid≡ _ _ (idEquiv _)
 --   λ x y → propBiimpl→Equiv {!snd (fst (snd M)) _ _!} {!!} {!!} {!!}
 
 --  -- where open BinaryRelation.isEquivRel (snd (snd M)) renaming (transitive' to _⊚_)

 -- -- PullbackSetoid = PullbackSetoidP i0
