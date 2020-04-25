{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Foundations.GroupoidLaws

data Smash (A B : Pointed₀) : Type₀ where
  basel : Smash A B
  baser : Smash A B
  proj  : (x : typ A) → (y : typ B) → Smash A B
  gluel : (a : typ A) → proj a (pt B) ≡ basel
  gluer : (b : typ B) → proj (pt A) b ≡ baser

-- Commutativity
comm : {A B : Pointed₀} → Smash A B → Smash B A
comm basel       = baser
comm baser       = basel
comm (proj x y)  = proj y x
comm (gluel a i) = gluer a i
comm (gluer b i) = gluel b i

commK : ∀ {A B : Pointed₀} → (x : Smash A B) → comm (comm x) ≡ x
commK basel       = refl
commK baser       = refl
commK (proj x y)  = refl
commK (gluel a x) = refl
commK (gluer b x) = refl

-- WIP below

SmashPt : (A B : Pointed₀) → Pointed₀
SmashPt A B = (Smash A B , basel)

-- -- A (B C) = C (B A) = C (A B) = (A B) C
-- rearrange : ∀ {A B C : Pointed₀} → Smash A (SmashPt B C) → Smash C (SmashPt B A)
-- rearrange basel = baser
-- rearrange baser = basel
-- rearrange {B = B} {C = C} (proj x basel) = proj (pt C) baser
-- rearrange {C = C} (proj x baser) = proj (pt C) basel  -- ?
-- rearrange (proj x (proj y z)) = proj z (proj y x)
-- rearrange {C = C} (proj x (gluel a i)) = proj (pt C) {!!}
-- rearrange (proj x (gluer b i)) = {!!}
-- rearrange (gluel a i) = {!!}
-- rearrange (gluer b i) = {!gluel ? i!}



--- Alternative definition

_⋁_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_⋁_ (A , ptA) (B , ptB) = Pushout {A = Unit} {B = A} {C = B} (λ {tt → ptA}) (λ {tt → ptB})

i∧ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋁ B → (typ A) × (typ B)
i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

_⋀_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_⋀_ A B = Pushout {A = (A ⋁ B)} {B = Unit} {C = (typ A) × (typ B)} (λ _ → tt) i∧


_⋀⃗_ : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} {D : Pointed ℓ'''} (f : A →∙ C) (g : B →∙ D)  → A ⋀ B → C ⋀ D
(f ⋀⃗ g) (inl tt) = inl tt
((f , fpt) ⋀⃗ (g , gpt)) (inr (x , x₁)) = inr (f x , g x₁)
_⋀⃗_ {B = B} {D = D} (f ,  fpt) (b , gpt)  (push (inl x) i) = (push (inl (f x)) ∙ (λ i → inr (f x , gpt (~ i)))) i
_⋀⃗_ {A = A} {B = B} {C = C} {D = D} (f , fpt) (g , gpt) (push (inr x) i) = (push (inr (g x)) ∙ (λ i → inr (fpt (~ i) , g x))) i
_⋀⃗_ {A = A} {B = B} {C = C} {D = D} (f , fpt) (g , gpt) (push (push tt j) i) = helper (~ j) i
  where
  helper : Path (Path (C ⋀ D) (inl tt) (inr ((f (pt A)) , (g (pt B)))))
                (push (inr (g (pt B))) ∙ λ i → inr ((fpt (~ i)) , (g (pt B))))
                (push (inl (f (pt A))) ∙ λ i → inr ((f (pt A)) , (gpt (~ i))))
  helper = (λ j → rUnit (push (inr (g (pt B)))) j ∙ λ i → inr ((fpt (~ i)) , (g (pt B))) ) ∙
           (λ j → (push (inr (gpt j)) ∙ λ i → inr ((pt C) , (gpt ((~ i) ∧ j)))) ∙ λ i → inr ((fpt (~ i)) , (g (pt B)))) ∙
           (λ j → (cong (push) (push tt) (~ j) ∙ λ i → inr (pt C , gpt (~ i))) ∙ λ i → inr ((fpt (~ i)) , (g (pt B)))) ∙
           (λ j → (push (inl (fpt (~ j))) ∙ λ i → inr (fpt ((~ j) ∨ i) , (gpt (~ i)))) ∙ λ i → inr ((fpt (~ i)) , (g (pt B)))) ∙
           (λ j → (push (inl (f (pt A))) ∙ λ i → inr (fpt (i ∧ (~ j)) , gpt ((~ i) ∨ j))) ∙ λ i → inr ((fpt ((~ i) ∧ (~ j))) , (gpt ((~ i) ∧ j)))) ∙
           (λ j → (rUnit (push (inl (f (pt A)))) (~ j)) ∙ λ i → inr ((f (pt A)) , (gpt (~ i))))


⋀-commuter : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋀ B → B ⋀ A
⋀-commuter (inl tt) = inl tt
⋀-commuter (inr (x , x₁)) = inr (x₁ , x)
⋀-commuter (push (inl x) i) = push (inr x) i
⋀-commuter (push (inr x) i) = push (inl x) i
⋀-commuter (push (push a i₁) i) = push (push (tt) (~ i₁)) i


⋀-comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → Iso (A ⋀ B) (B ⋀ A)
Iso.fun ⋀-comm = ⋀-commuter
Iso.inv ⋀-comm = ⋀-commuter
Iso.rightInv ⋀-comm (inl tt) = refl
Iso.rightInv ⋀-comm (inr (x , x₁)) = refl
Iso.rightInv ⋀-comm (push (inl x) i) = refl
Iso.rightInv ⋀-comm (push (inr x) i) = refl
Iso.rightInv ⋀-comm (push (push a i₁) i) = refl
Iso.leftInv ⋀-comm (inl tt) = refl
Iso.leftInv ⋀-comm (inr (x , x₁)) = refl
Iso.leftInv ⋀-comm (push (inl x) i) = refl
Iso.leftInv ⋀-comm (push (inr x) i) = refl
Iso.leftInv ⋀-comm (push (push a i₁) i) = refl

rearrange-proj : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} → A ⋀ B → (C ⋀ B , inl tt) ⋀ A
rearrange-proj (inl x) = inl tt
rearrange-proj {C = C} (inr (x , x₁)) = inr (inr ((snd C) , x₁) , x)
rearrange-proj {A = A}{B = B} {C = C} (push (inl x) i) = (push (inr x) ∙ (λ i → inr (push (inr (snd B)) i , x))) i
rearrange-proj {A = A}{B = B} {C = C} (push (inr x) i) = (push (inr (snd A)) ∙ (λ i → inr (push (inr x) i , snd A))) i
rearrange-proj {A = A}{B = B} {C = C} (push (push a i₁) i) = (push (inr (snd A)) ∙ (λ i → inr (push (inr (snd B)) i , (snd A)))) i
