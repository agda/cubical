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

_⋀∙_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = Pushout {A = (A ⋁ B)} {B = Unit} {C = (typ A) × (typ B)} (λ _ → tt) i∧ , (inl tt) 


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

⋀-associate : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} → A ⋀ (B ⋀∙ C) → (C ⋀∙ B) ⋀ A
⋀-associate (inl x) = inl tt
⋀-associate (inr (x , inl x₁)) = inr ((inl tt) , x)
⋀-associate (inr (x , inr (x₁ , x₂))) = inr ((inr (x₂ , x₁)) , x)
⋀-associate (inr (x , push (inl x₁) i)) = inr (push (inr x₁) i , x)
⋀-associate (inr (x , push (inr x₁) i)) = inr (push (inl x₁) i , x)
⋀-associate (inr (x , push (push a i₁) i)) = inr (push (push tt (~ i₁)) i , x)
⋀-associate (push (inl x) i) = push (inr x) i
⋀-associate {A = A} (push (inr (inl tt)) i) = push (inr (snd A)) i
⋀-associate (push (inr (inr (x , x₁))) i) = push (inl (inr (x₁ , x))) i
⋀-associate {A = A} {B = B} {C = C} (push (inr (push (inl x) j)) i) =
  hcomp (λ k → λ { (i = i0) → inl tt
                  ; (i = i1) → (inr (push (inr x) j , snd A))
                  ; (j = i0) → push (push tt k) i
                  ; (j = i1) → push (inl (inr (snd C , x))) i})
        (push (inl (push (inr x) j)) i)
⋀-associate {A = A} {B = B} {C = C} (push (inr (push (inr x) j)) i) =
  hcomp ((λ k → λ { (i = i0) → inl tt
                   ; (i = i1) → inr (push (inl x) j , snd A)
                   ; (j = i0) → push (push tt k) i
                   ; (j = i1) → push (inl (inr (x , snd B))) i}))
        (push (inl (push (inl x) j)) i)
⋀-associate {A = A} {B = B} {C = C} (push (inr (push (push tt z) j)) i) =
  hcomp (λ k → λ { (i = i0) → inl tt
                  ; (i = i1) → inr ((push (push tt (~ z)) j) , (snd A))
                  ; (j = i0) → push (push tt k) i
                  ; (j = i1) → push (inl (inr (snd C , (snd B)))) i
                  })
        (push (inl (push (push tt (~ z)) j)) i)
⋀-associate {A = A} (push (push a i₁) i) = push (inr (snd A)) i

⋀-associate⁻ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} → (C ⋀∙ B) ⋀ A → A ⋀ (B ⋀∙ C)
⋀-associate⁻ (inl x) = inl tt
⋀-associate⁻ (inr (inl x , x₁)) = inr (x₁ , (inl tt))
⋀-associate⁻ (inr (inr (x , x₂) , x₁)) = inr (x₁ , (inr (x₂ , x)))
⋀-associate⁻ (inr (push (inl x) i , x₁)) = inr (x₁ , push (inr x) i)
⋀-associate⁻ (inr (push (inr x) i , x₁)) = inr (x₁ , push (inl x) i)
⋀-associate⁻ (inr (push (push a i₁) i , x)) = inr (x , push (push tt (~ i₁)) i)
⋀-associate⁻ {A = A} (push (inl (inl x)) i) = push (inl (snd A)) i
⋀-associate⁻ (push (inl (inr (x , x₁))) i) = push (inr (inr (x₁ , x))) i
⋀-associate⁻ {A = A} {B = B} (push (inl (push (inl x) j)) i) =
  hcomp (λ k → λ {(i = i0) → inl tt
                 ; (i = i1) → inr (snd A , push (inr x) j)
                 ; (j = i0) → push (push tt (~ k)) i
                 ; (j = i1) → push (inr (inr ((snd B) , x))) i})
        (push (inr (push (inr x) j)) i)
⋀-associate⁻ {A = A} {C = C} (push (inl (push (inr x) j)) i) = 
  hcomp (λ k → λ {(i = i0) → inl tt
                ; (i = i1) → inr (snd A , push (inl x) j)
                ; (j = i0) → push (push tt (~ k)) i
                ; (j = i1) → push (inr (inr (x , (snd C)))) i})
        (push (inr (push (inl x) j)) i)
⋀-associate⁻ {A = A} {B = B} {C = C} (push (inl (push (push a z) j)) i) =
  hcomp (λ k → λ { (i = i0) → inl tt
                  ; (i = i1) → inr (snd A , (push (push tt (~ z)) j))
                  ; (j = i0) → push (push tt (~ k)) i
                  ; (j = i1) → push (inr (inr (snd B , snd C))) i 
                  })
        (push (inr (push (push tt (~ z)) j)) i)
⋀-associate⁻ (push (inr x) i) = push (inl x) i
⋀-associate⁻ {A = A} (push (push a i₁) i) = push (inl (snd A)) i

⋀-Iso : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} → Iso (A ⋀ (B ⋀∙ C)) ((C ⋀∙ B) ⋀ A)
Iso.fun ⋀-Iso = ⋀-associate
Iso.inv ⋀-Iso = ⋀-associate⁻
Iso.rightInv ⋀-Iso (inl x) = refl
Iso.rightInv ⋀-Iso (inr (inl x , x₁)) = refl
Iso.rightInv ⋀-Iso (inr (inr (x , x₂) , x₁)) = refl
Iso.rightInv ⋀-Iso (inr (push (inl x) i , x₁)) z = inr (push (inl x) i , x₁)
Iso.rightInv ⋀-Iso (inr (push (inr x) i , x₁)) z = inr (push (inr x) i , x₁)
Iso.rightInv ⋀-Iso (inr (push (push tt j) i , x₁)) z = inr (push (push tt j) i , x₁)
Iso.rightInv ⋀-Iso (push (inl (inl x)) i) z = push (push tt (~ z)) i
Iso.rightInv ⋀-Iso (push (inl (inr (x , x₁))) i) j = push (inl (inr (x , x₁))) i
Iso.rightInv ⋀-Iso (push (inl (push (inl x) i₁)) i) = {!!}
Iso.rightInv ⋀-Iso (push (inl (push (inr x) i₁)) i) = {!!}
Iso.rightInv ⋀-Iso (push (inl (push (push a i₂) i₁)) i) = {!a!}
Iso.rightInv ⋀-Iso (push (inr x) i) = {!!}
Iso.rightInv ⋀-Iso (push (push a i₁) i) = {!!}
Iso.leftInv ⋀-Iso = {!!}
