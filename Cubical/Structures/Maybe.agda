{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

MaybeStructure : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
MaybeStructure S X = Maybe (S X)

MaybeRel : {A B : Type ℓ} (R : A → B → Type ℓ₁) → Maybe A → Maybe B → Type ℓ₁
MaybeRel R nothing nothing = Lift Unit
MaybeRel R nothing (just _) = Lift ⊥
MaybeRel R (just _) nothing = Lift ⊥
MaybeRel R (just x) (just y) = R x y

MaybeRel-cong : {A B : Type ℓ} {R : A → B → Type ℓ₁} {S : A → B → Type ℓ₁'}
  → (∀ x y → R x y ≃ S x y)
  → ∀ ox oy → MaybeRel R ox oy ≃ MaybeRel S ox oy
MaybeRel-cong e nothing nothing = Lift≃Lift (idEquiv _)
MaybeRel-cong e nothing (just _) = Lift≃Lift (idEquiv _)
MaybeRel-cong e (just _) nothing = Lift≃Lift (idEquiv _)
MaybeRel-cong e (just x) (just y) = e x y

module MaybePathP where

  Code : (A : I → Type ℓ) → Maybe (A i0) → Maybe (A i1) → Type ℓ
  Code A = MaybeRel (PathP A)

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

MaybeEquivStr : {S : Type ℓ → Type ℓ₁}
  → StrEquiv S ℓ₁' → StrEquiv (MaybeStructure S) ℓ₁'
MaybeEquivStr ι (X , ox) (Y , oy) e = MaybeRel (λ x y → ι (X , x) (Y , y) e) ox oy

maybeUnivalentStr : {S : Type ℓ → Type ℓ₁} (ι : StrEquiv S ℓ₁')
  → UnivalentStr S ι → UnivalentStr (MaybeStructure S) (MaybeEquivStr ι)
maybeUnivalentStr ι θ {X , ox} {Y , oy} e =
  compEquiv
    (MaybeRel-cong (λ x y → θ {X , x} {Y , y} e) ox oy)
    (MaybePathP.Code≃PathP ox oy)
