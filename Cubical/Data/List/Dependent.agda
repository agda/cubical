{-# OPTIONS --safe #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Nat

module Cubical.Data.List.Dependent where

open _≅_

data ListP {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) : (as : List A) → Type (ℓ-max ℓA ℓB) where
  [] : ListP B []
  _∷_ : {x : A} (y : B x) {xs : List A} (ys : ListP B xs) → ListP B (x ∷ xs)

-- Represent ListP via known operations in order to derive properties more easily.
RepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → Type (ℓ-max ℓA ℓB)
RepListP B [] = Lift Unit
RepListP B (a ∷ as) = B a × RepListP B as

isoRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≅ RepListP B as
fun (isoRepListP B []) bs = lift tt
inv (isoRepListP B []) u = []
rightInv (isoRepListP B []) u = refl
leftInv (isoRepListP B []) [] = refl
fun (isoRepListP B (a ∷ as)) (b ∷ bs) = b , fun (isoRepListP B as) bs
inv (isoRepListP B (a ∷ as)) (b , br) = b ∷ inv (isoRepListP B as) br
rightInv (isoRepListP B (a ∷ as)) (b , br) i = b , rightInv (isoRepListP B as) br i
leftInv (isoRepListP B (a ∷ as)) (b ∷ bs) i = b ∷ leftInv (isoRepListP B as) bs i

equivRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≃ RepListP B as
equivRepListP B as = isoToEquiv (isoRepListP B as)

pathRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≡ RepListP B as
pathRepListP B as = ua (equivRepListP B as)

private
  isOfHLevelSucSuc-RepListP : ∀ {ℓA ℓB} (n : HLevel)
    → {A : Type ℓA}
    → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
    → (as : List A)
    → isOfHLevel (suc (suc n)) (RepListP B as)
  isOfHLevelSucSuc-RepListP n isHB [] = isOfHLevelLift (suc (suc n)) (isOfHLevelUnit (suc (suc n)))
  isOfHLevelSucSuc-RepListP n isHB (a ∷ as) = isOfHLevelProd (suc (suc n)) (isHB a) (isOfHLevelSucSuc-RepListP n isHB as)

isOfHLevelSucSuc-ListP : ∀ {ℓA ℓB} (n : HLevel)
  → {A : Type ℓA}
  → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
  → {as : List A}
  → isOfHLevel (suc (suc n)) (ListP B as)
isOfHLevelSucSuc-ListP n {A} {B} isHB {as} =
  subst⁻ (isOfHLevel (suc (suc n))) (pathRepListP B as) (isOfHLevelSucSuc-RepListP n isHB as)

--------------------------

mapP : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (f : A → A') (g : (a : A) → B a → B' (f a)) → ∀ as → ListP B as → ListP B' (map f as)
mapP f g [] [] = []
mapP f g (a ∷ as) (b ∷ bs) = g _ b ∷ mapP f g as bs

mapOverIdfun : ∀ {ℓA ℓB ℓB'} {A : Type ℓA} {B : A → Type ℓB} {B' : A → Type ℓB'}
  (g : (a : A) → B a → B' a) → ∀ as → ListP B as → ListP B' as
mapOverIdfun g [] [] = []
mapOverIdfun g (a ∷ as) (b ∷ bs) = g a b ∷ mapOverIdfun g as bs

mapOverIdfun-idfun : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} as → mapOverIdfun (λ a → idfun _) as ≡ (idfun (ListP B as))
mapOverIdfun-idfun [] i [] = []
mapOverIdfun-idfun (a ∷ as) i (b ∷ bs) = b ∷ mapOverIdfun-idfun as i bs

mapOverIdfun-∘ : ∀ {ℓA ℓB ℓB' ℓB''} {A : Type ℓA} {B : A → Type ℓB} {B' : A → Type ℓB'} {B'' : A → Type ℓB''}
  (h : (a : A) → B' a → B'' a) (g : (a : A) → B a → B' a) → ∀ as
  → mapOverIdfun (λ a → h a ∘ g a) as ≡ mapOverIdfun h as ∘ mapOverIdfun g as
mapOverIdfun-∘ h g [] i [] = []
mapOverIdfun-∘ h g (a ∷ as) i (b ∷ bs) = h a (g a b) ∷ mapOverIdfun-∘ h g as i bs

