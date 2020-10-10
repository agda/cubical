{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Sum.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty
open import Cubical.Data.Nat

open import Cubical.Data.Sum.Base

-- Path space of sum type
module SumPath {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  Cover : A ⊎ B → A ⊎ B → Type (ℓ-max ℓ ℓ')
  Cover (inl a) (inl a') = Lift {j = ℓ-max ℓ ℓ'} (a ≡ a')
  Cover (inl _) (inr _) = Lift ⊥
  Cover (inr _) (inl _) = Lift ⊥
  Cover (inr b) (inr b') = Lift {j = ℓ-max ℓ ℓ'} (b ≡ b')

  reflCode : (c : A ⊎ B) → Cover c c
  reflCode (inl a) = lift refl
  reflCode (inr b) = lift refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode (inl a) (inl a') (lift p) = cong inl p
  decode (inl a) (inr b') ()
  decode (inr b) (inl a') ()
  decode (inr b) (inr b') (lift q) = cong inr q

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl (inl a) = refl
  decodeRefl (inr b) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode (inl a) (inl _) (lift d) =
    J (λ a' p → encode (inl a) (inl a') (cong inl p) ≡ lift p) (encodeRefl (inl a)) d
  encodeDecode (inr a) (inr _) (lift d) =
    J (λ a' p → encode (inr a) (inr a') (cong inr p) ≡ lift p) (encodeRefl (inr a)) d

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' =
    isoToEquiv (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → isOfHLevel (suc (suc n)) B
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p q (inl a) (inl a') = isOfHLevelLift (suc n) (p a a')
  isOfHLevelCover n p q (inl a) (inr b') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inl a') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inr b') = isOfHLevelLift (suc n) (q b b')

isEmbedding-inl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isEmbedding (inl {A = A} {B = B})
isEmbedding-inl w z = snd (compEquiv LiftEquiv (SumPath.Cover≃Path (inl w) (inl z)))

isEmbedding-inr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isEmbedding (inr {A = A} {B = B})
isEmbedding-inr w z = snd (compEquiv LiftEquiv (SumPath.Cover≃Path (inr w) (inr z)))

isOfHLevelSum : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) B
  → isOfHLevel (suc (suc n)) (A ⊎ B)
isOfHLevelSum n lA lB c c' =
  isOfHLevelRetract (suc n)
    (SumPath.encode c c')
    (SumPath.decode c c')
    (SumPath.decodeEncode c c')
    (SumPath.isOfHLevelCover n lA lB c c')

isSetSum : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isSet A → isSet B → isSet (A ⊎ B)
isSetSum = isOfHLevelSum 0

isGroupoidSum : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isGroupoid A → isGroupoid B → isGroupoid (A ⊎ B)
isGroupoidSum = isOfHLevelSum 1

is2GroupoidSum : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → is2Groupoid A → is2Groupoid B → is2Groupoid (A ⊎ B)
is2GroupoidSum = isOfHLevelSum 2

sumIso : ∀ {ℓa ℓb ℓc ℓd} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {D : Type ℓd}
       → Iso A C → Iso B D
       → Iso (A ⊎ B) (C ⊎ D)
Iso.fun (sumIso iac ibd) (inl x) = inl (iac .Iso.fun x)
Iso.fun (sumIso iac ibd) (inr x) = inr (ibd .Iso.fun x)
Iso.inv (sumIso iac ibd) (inl x) = inl (iac .Iso.inv x)
Iso.inv (sumIso iac ibd) (inr x) = inr (ibd .Iso.inv x)
Iso.rightInv (sumIso iac ibd) (inl x) = cong inl (iac .Iso.rightInv x)
Iso.rightInv (sumIso iac ibd) (inr x) = cong inr (ibd .Iso.rightInv x)
Iso.leftInv (sumIso iac ibd) (inl x) = cong inl (iac .Iso.leftInv x)
Iso.leftInv (sumIso iac ibd) (inr x) = cong inr (ibd .Iso.leftInv x)
