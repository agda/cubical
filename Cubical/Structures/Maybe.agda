{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

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

-- Structured isomorphism

maybe-structure : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
maybe-structure S X = Maybe (S X)

maybe-iso : {S : Type ℓ → Type ℓ₁}
  → StrIso S ℓ₁' → StrIso (maybe-structure S) ℓ₁'
maybe-iso ι (X , ox) (Y , oy) e = maybe-rel (λ x y → ι (X , x) (Y , y) e) ox oy

maybe-is-SNS : {S : Type ℓ → Type ℓ₁} (ι : StrIso S ℓ₁')
  → SNS S ι → SNS (maybe-structure S) (maybe-iso ι)
maybe-is-SNS ι θ {X , ox} {Y , oy} e =
  compEquiv
    (maybe-rel-cong (λ x y → θ {X , x} {Y , y} e) ox oy)
    (MaybePathP.Code≃PathP ox oy)

-- Structured relation

maybe-setStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₁
maybe-setStructure S .struct X = Maybe (S .struct X)
maybe-setStructure S .set setX = isOfHLevelMaybe 0 (S .set setX)

maybe-propRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (λ X → Maybe (S X)) ℓ₁'
maybe-propRel ρ .rel X Y R = maybe-rel (ρ .rel X Y R)
maybe-propRel ρ .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
maybe-propRel ρ .prop propR nothing (just y) = isOfHLevelLift 1 isProp⊥
maybe-propRel ρ .prop propR (just x) nothing = isOfHLevelLift 1 isProp⊥
maybe-propRel ρ .prop propR (just x) (just y) = ρ .prop propR x y

open isSNRS
open BisimDescends

isSNRSMaybe : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁')
  → isSNRS S ρ
  → isSNRS (maybe-setStructure S) (maybe-propRel ρ)
isSNRSMaybe S ρ θ .propQuo {X , nothing} R (nothing , lift tt) (nothing , lift tt) = refl
isSNRSMaybe S ρ θ .propQuo {X , just x} R (just x' , p) (just y' , q) =
  cong (λ {(z , r) → (just z , r)}) (θ .propQuo R (x' , p) (y' , q))
isSNRSMaybe S ρ θ .descends {X , nothing} R .fst code .quoᴸ = nothing , _
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .quoᴸ =
  just (θ .descends R .fst code .quoᴸ .fst) , θ .descends R .fst code .quoᴸ .snd
isSNRSMaybe S ρ θ .descends {B = Y , nothing} R .fst code .quoᴿ = nothing , _
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .quoᴿ =
  just (θ .descends R .fst code .quoᴿ .fst) , θ .descends R .fst code .quoᴿ .snd
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , nothing} R .fst code .path i = nothing
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .path i =
  just (θ .descends R .fst code .path i)
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , nothing} R .snd d = _
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | nothing , _ | just y' , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
isSNRSMaybe S ρ θ .descends {X , just x} {Y , nothing} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , _ | nothing , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , c | just y' , c' | p =
  θ .descends R .snd d'
  where
  d' : BisimDescends (S .struct) ρ (X , x) (Y , y) R
  d' .quoᴸ = x' , c
  d' .quoᴿ = y' , c'
  d' .path = MaybePathP.encode _ _ _ p
