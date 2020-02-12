{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Properties where


open import Cubical.ZCohomology.Base
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_ ; 1+_ to 1+₋₂_)
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
private
  variable
    ℓ : Level
    A : Type ℓ





{- Equivalence between cohomology and the reduced version -}
coHom↔coHomRed : ∀ {ℓ} → (n : ℕ₋₂) → (A : Set ℓ) → (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHom↔coHomRed neg2 A i = ∥ helplemma {C = (Int , pos 0)} i ∥₀
  module ClaireCaron where
  helplemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →* C)))
  helplemma {C = C} = isoToPath (iso map1 map2 (λ b → linvPf b) (λ a  → refl)) where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →* C))
    map1 f = map1' , refl module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →* C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)
    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →* C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j) where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x 
      helper (inl x) = refl
      helper (inr tt) = sym snd
      
coHom↔coHomRed (suc n) A i = ∥ ClaireCaron.helplemma A i {C = ((K (suc n)) , ∣ north ∣)} i ∥₀




{- Unfinished proof that Kₙ ≡ Ω Kₙ₊₁  -}

invPathCancel : {a b : A} → (p : a ≡ b) → p ∙ (sym p) ≡ refl
invPathCancel {a = a} {b = b} p = J {x = a} (λ y p → p ∙ (sym p) ≡ refl ) (sym (lUnit refl)) p

φ : (a : A) → A → (north {A = A} ≡ north {A = A})
φ x = (λ a → ((merid  a) ∙ sym ((merid x))))

φ* : (A : Pointed ℓ) → A →* Ω ((Susp (typ A)) , north)
φ* A = (φ (pt A)) , invPathCancel (merid (pt A))

σ : (n : ℕ₋₂) → (typ (K-ptd n)) → (typ (Ω (K-ptd (suc n))))
σ neg2 k = looper k  ( cong {B = λ _ → (∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1)}
                     (λ x → ∣ x ∣)
                     ((merid north) ∙ (sym (merid south))) )
  where                   
  looper : ∀ {ℓ} → {A : Type ℓ} → {a : A} → (n : Int) → (a ≡ a) → (a ≡ a) -- defining loopⁿ
  looper {A = A} {a = a} (pos zero) p = refl
  looper {A = A} {a = a} (pos (suc n)) p = (looper (pos n) p) ∙ p
  looper {A = A} {a = a} (negsuc zero) p = sym p
  looper {A = A} {a = a} (negsuc (suc n)) p = (sym p) ∙ (looper (negsuc n) p)
σ (suc n) x = rec {n = suc (suc (suc n))}
                  {B = (typ (Ω (K-ptd  (suc (suc n)))))}
                  (isOfHLevel∥∥ {A = S₊ (2+ suc (suc n))} (suc (suc (suc (suc n)))) ∣ north ∣ ∣ north ∣)
                  (λ y → cong {B = λ _ → Null (S (1+₋₂ (suc (suc (suc (suc n)))))) (S₊ (2+ (suc (suc n))))}
                              (λ z → ∣ z ∣)
                              (φ north y))
                  x 




