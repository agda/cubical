{-# OPTIONS --safe #-}
module Cubical.HITs.S1.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Cubes
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.HITs.S1.Base
open import Cubical.HITs.PropositionalTruncation as PropTrunc hiding ( rec ; elim )

private
  variable
    ℓ : Level
    A : Type ℓ

rec : (b : A) (l : b ≡ b) → S¹ → A
rec b l base     = b
rec b l (loop i) = l i

elim : (C : S¹ → Type ℓ) (b : C base) (l : PathP (λ i → C (loop i)) b b) → (x : S¹) → C x
elim _ b l base     = b
elim _ b l (loop i) = l i

isConnectedS¹ : (s : S¹) → ∥ base ≡ s ∥₁
isConnectedS¹ base = ∣ refl ∣₁
isConnectedS¹ (loop i) =
  squash₁ ∣ (λ j → loop (i ∧ j)) ∣₁ ∣ (λ j → loop (i ∨ ~ j)) ∣₁ i

isGroupoidS¹ : isGroupoid S¹
isGroupoidS¹ s t =
  PropTrunc.rec isPropIsSet
    (λ p →
      subst (λ s → isSet (s ≡ t)) p
        (PropTrunc.rec isPropIsSet
          (λ q → subst (λ t → isSet (base ≡ t)) q isSetΩS¹)
          (isConnectedS¹ t)))
    (isConnectedS¹ s)

IsoFunSpaceS¹ : Iso (S¹ → A) (Σ[ x ∈ A ] x ≡ x)
Iso.fun IsoFunSpaceS¹ f = (f base) , (cong f loop)
Iso.inv IsoFunSpaceS¹ (x , p) base = x
Iso.inv IsoFunSpaceS¹ (x , p) (loop i) = p i
Iso.rightInv IsoFunSpaceS¹ (x , p) = refl
Iso.leftInv IsoFunSpaceS¹ f = funExt λ {base → refl ; (loop i) → refl}


Iso∂Cube2S₁→ : Iso (S¹ → A) (∂Cube 2 A)
Iso.fun Iso∂Cube2S₁→ x = (_ , cong x loop) , (_ , refl) , refl
Iso.inv Iso∂Cube2S₁→ ((_ , p) , (_ , q) , r) = rec _  
  (p ∙ (cong snd r ∙' (sym q ∙' sym (cong fst r))))
Iso.rightInv Iso∂Cube2S₁→ ((_ , p) , (_ , q) , r) = 
 ΣPathP ((ΣPathP (cong₂ _,_ _ _ ,  symP (compPath-filler _ _))) ,
   ΣPathP (ΣPathP (cong₂ _,_ _ _ , fill₋₁) ,
    Square× (λ i j → fst (r (i ∧ j))) (congP (λ _ →  symP) fill₋₁)))

Iso.leftInv Iso∂Cube2S₁→ a = funExt (elim _ refl
  (flipSquare (cong ((cong a loop) ∙_)
      (λ i → rUnit (lUnit refl (~ i)) (~ i)) ∙ sym (rUnit _))))
