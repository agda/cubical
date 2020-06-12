{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Option where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

option-structure : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
option-structure S X = Unit ⊎ S X

option-rel : {A B : Type ℓ} (R : A → B → Type ℓ₁) → Unit ⊎ A → Unit ⊎ B → Type ℓ₁
option-rel R (inl _) (inl _) = Lift Unit
option-rel R (inl _) (inr _) = Lift ⊥
option-rel R (inr _) (inl _) = Lift ⊥
option-rel R (inr x) (inr y) = R x y

option-rel-cong : {A B : Type ℓ} {R : A → B → Type ℓ₁} {S : A → B → Type ℓ₁'}
  → (∀ x y → R x y ≃ S x y)
  → ∀ ox oy → option-rel R ox oy ≃ option-rel S ox oy
option-rel-cong e (inl _) (inl _) = Lift≃Lift (idEquiv _)
option-rel-cong e (inl _) (inr _) = Lift≃Lift (idEquiv _)
option-rel-cong e (inr _) (inl _) = Lift≃Lift (idEquiv _)
option-rel-cong e (inr x) (inr y) = e x y

module OptionPathP where

  Code : (A : I → Type ℓ) → Unit ⊎ A i0 → Unit ⊎ A i1 → Type ℓ
  Code A = option-rel (PathP A)

  encodeRefl : {A : Type ℓ} → ∀ ox → Code (λ _ → A) ox ox
  encodeRefl (inl _) = lift tt
  encodeRefl (inr _) = refl

  encode : (A : I → Type ℓ) → ∀ ox oy → PathP (λ i → Unit ⊎ A i) ox oy → Code A ox oy
  encode A ox oy p = transport (λ j → Code (λ i → A (i ∧ j)) ox (p j)) (encodeRefl ox)

  decode : {A : I → Type ℓ} → ∀ ox oy → Code A ox oy → PathP (λ i → Unit ⊎ A i) ox oy
  decode (inl _) (inl _) p i = inl _
  decode (inr _) (inr _) p i = inr (p i)

  decodeEncodeRefl : {A : Type ℓ} (ox : Unit ⊎ A) → decode ox ox (encodeRefl ox) ≡ refl
  decodeEncodeRefl (inl _) = refl
  decodeEncodeRefl (inr _) = refl

  decodeEncode : {A : I → Type ℓ} → ∀ ox oy p → decode ox oy (encode A ox oy p) ≡ p
  decodeEncode {A = A} ox oy p =
    transport
      (λ k →
        decode _ _ (transp (λ j → Code (λ i → A (i ∧ j ∧ k)) ox (p (j ∧ k))) (~ k) (encodeRefl ox))
        ≡ (λ i → p (i ∧ k)))
      (decodeEncodeRefl ox)

  encodeDecode : (A : I → Type ℓ) → ∀ ox oy c → encode A ox oy (decode ox oy c) ≡ c
  encodeDecode A (inl _) (inl _) c = refl
  encodeDecode A (inr x) (inr y) c =
    transport
      (λ k →
        encode (λ i → A (i ∧ k)) _ _ (decode (inr x) (inr (c k)) (λ i → c (i ∧ k)))
        ≡ (λ i → c (i ∧ k)))
      (transportRefl _)

  Code≃PathP : {A : I → Type ℓ} → ∀ ox oy → Code A ox oy ≃ PathP (λ i → Unit ⊎ A i) ox oy
  Code≃PathP {A = A} ox oy = isoToEquiv isom
    where
    isom : Iso _ _
    isom .Iso.fun = decode ox oy
    isom .Iso.inv = encode _ ox oy
    isom .Iso.rightInv = decodeEncode ox oy
    isom .Iso.leftInv = encodeDecode A ox oy
  
option-iso : {S : Type ℓ → Type ℓ₁}
  → StrIso S ℓ₁' → StrIso (option-structure S) ℓ₁'
option-iso ι (X , ox) (Y , oy) e = option-rel (λ x y → ι (X , x) (Y , y) e) ox oy

option-is-SNS : {S : Type ℓ → Type ℓ₁} (ι : StrIso S ℓ₁')
  → SNS S ι → SNS (option-structure S) (option-iso ι)
option-is-SNS ι θ {X , ox} {Y , oy} e =
  compEquiv
    (option-rel-cong (λ x y → θ {X , x} {Y , y} e) ox oy)
    (OptionPathP.Code≃PathP ox oy)
