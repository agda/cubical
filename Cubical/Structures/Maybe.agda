{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

maybe-structure : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
maybe-structure S X = Maybe (S X)

maybe-rel : {A B : Type ℓ} (R : A → B → Type ℓ₁) → Maybe A → Maybe B → Type ℓ₁
maybe-rel R nothing nothing = Lift Unit
maybe-rel R nothing (just _) = Lift ⊥
maybe-rel R (just _) nothing = Lift ⊥
maybe-rel R (just x) (just y) = R x y

maybe-rel-cong : {A B : Type ℓ} {R : A → B → Type ℓ₁} {S : A → B → Type ℓ₁'}
  → (∀ x y → R x y ≃ S x y)
  → ∀ ox oy → maybe-rel R ox oy ≃ maybe-rel S ox oy
maybe-rel-cong e nothing nothing = Lift≃Lift (idEquiv _)
maybe-rel-cong e nothing (just _) = Lift≃Lift (idEquiv _)
maybe-rel-cong e (just _) nothing = Lift≃Lift (idEquiv _)
maybe-rel-cong e (just x) (just y) = e x y

module MaybePathP where

  Code : (A : I → Type ℓ) → Maybe (A i0) → Maybe (A i1) → Type ℓ
  Code A = maybe-rel (PathP A)

  encodeRefl : {A : Type ℓ} → ∀ ox → Code (λ _ → A) ox ox
  encodeRefl nothing = lift tt
  encodeRefl (just _) = refl

  encode : (A : I → Type ℓ) → ∀ ox oy → PathP (λ i → Maybe (A i)) ox oy → Code A ox oy
  encode A ox oy p = transport (λ j → Code (λ i → A (i ∧ j)) ox (p j)) (encodeRefl ox)

  decode : {A : I → Type ℓ} → ∀ ox oy → Code A ox oy → PathP (λ i → Maybe (A i)) ox oy
  decode nothing nothing p i = nothing
  decode (just _) (just _) p i = just (p i)

  decodeEncodeRefl : {A : Type ℓ} (ox : Maybe A) → decode ox ox (encodeRefl ox) ≡ refl
  decodeEncodeRefl nothing = refl
  decodeEncodeRefl (just _) = refl

  decodeEncode : {A : I → Type ℓ} → ∀ ox oy p → decode ox oy (encode A ox oy p) ≡ p
  decodeEncode {A = A} ox oy p =
    transport
      (λ k →
        decode _ _ (transp (λ j → Code (λ i → A (i ∧ j ∧ k)) ox (p (j ∧ k))) (~ k) (encodeRefl ox))
        ≡ (λ i → p (i ∧ k)))
      (decodeEncodeRefl ox)

  encodeDecode : (A : I → Type ℓ) → ∀ ox oy c → encode A ox oy (decode ox oy c) ≡ c
  encodeDecode A nothing nothing c = refl
  encodeDecode A (just x) (just y) c =
    transport
      (λ k →
        encode (λ i → A (i ∧ k)) _ _ (decode (just x) (just (c k)) (λ i → c (i ∧ k)))
        ≡ (λ i → c (i ∧ k)))
      (transportRefl _)

  Code≃PathP : {A : I → Type ℓ} → ∀ ox oy → Code A ox oy ≃ PathP (λ i → Maybe (A i)) ox oy
  Code≃PathP {A = A} ox oy = isoToEquiv isom
    where
    isom : Iso _ _
    isom .Iso.fun = decode ox oy
    isom .Iso.inv = encode _ ox oy
    isom .Iso.rightInv = decodeEncode ox oy
    isom .Iso.leftInv = encodeDecode A ox oy

maybe-iso : {S : Type ℓ → Type ℓ₁}
  → StrIso S ℓ₁' → StrIso (maybe-structure S) ℓ₁'
maybe-iso ι (X , ox) (Y , oy) e = maybe-rel (λ x y → ι (X , x) (Y , y) e) ox oy

maybe-is-SNS : {S : Type ℓ → Type ℓ₁} (ι : StrIso S ℓ₁')
  → SNS S ι → SNS (maybe-structure S) (maybe-iso ι)
maybe-is-SNS ι θ {X , ox} {Y , oy} e =
  compEquiv
    (maybe-rel-cong (λ x y → θ {X , x} {Y , y} e) ox oy)
    (MaybePathP.Code≃PathP ox oy)
