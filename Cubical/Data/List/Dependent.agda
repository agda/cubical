
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.List.FinData
open import Cubical.Data.Unit
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Nat

module Cubical.Data.List.Dependent where

open _≅_

data ListP {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) : (as : List A) → Type (ℓ-max ℓA ℓB) where
  [] : ListP B []
  _∷_ : {x : A} (y : B x) {xs : List A} (ys : ListP B xs) → ListP B (x ∷ xs)

infixr 5 _∷_

--------------------------

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

lookupP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as} (bs : ListP B as) → (p : Fin (length as)) → B (lookup as p)
lookupP (b ∷ bs) zero = b
lookupP (b ∷ bs) (suc p) = lookupP bs p

{- It seems sensible to reserve the name tabulateP for a function that mentions tabulate (rather than lookup) in its type.
-}
tabulateOverLookup : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} as (^b : (p : Fin (length as)) → B (lookup as p))
  → ListP B as
tabulateOverLookup [] ^b = []
tabulateOverLookup (a ∷ as) ^b = ^b zero ∷ tabulateOverLookup as (^b ∘ suc)

tabulateOverLookup-lookupP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as} (bs : ListP B as) →
  tabulateOverLookup as (lookupP bs) ≡ bs
tabulateOverLookup-lookupP [] = refl
tabulateOverLookup-lookupP (b ∷ bs) = cong (b ∷_) (tabulateOverLookup-lookupP bs)

lookupP-tabulateOverLookup : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) as (^b : (p : Fin (length as)) → B (lookup as p))
  → lookupP (tabulateOverLookup {B = B} as ^b) ≡ ^b
lookupP-tabulateOverLookup B (a ∷ as) ^b i zero = ^b zero
lookupP-tabulateOverLookup B (a ∷ as) ^b i (suc p) = lookupP-tabulateOverLookup B as (^b ∘ suc) i p

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

mapOverSpan : ∀ {ℓI ℓA ℓA' ℓB ℓB'} {I : Type ℓI} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (f : I → A) (f' : I → A') (g : ∀ i → B (f i) → B' (f' i)) → ∀ is → ListP B (map f is) → ListP B' (map f' is)
mapOverSpan f f' g [] [] = []
mapOverSpan f f' g (i ∷ is) (b ∷ bs) = g i b ∷ mapOverSpan f f' g is bs

mapOverSpan-idfun : ∀ {ℓI ℓA ℓB} {I : Type ℓI} {A : Type ℓA} {B : A → Type ℓB}
  (f : I → A) → ∀ is → mapOverSpan {B = B} f f (λ i a → a) is ≡ idfun _
mapOverSpan-idfun f [] j [] = []
mapOverSpan-idfun f (i ∷ is) j (b ∷ bs) = b ∷ mapOverSpan-idfun f is j bs

mapOverSpan-∘ : ∀ {ℓI ℓA ℓA' ℓA'' ℓB ℓB' ℓB''}
  {I : Type ℓI}
  {A : Type ℓA} {A' : Type ℓA'} {A'' : Type ℓA''}
  {B : A → Type ℓB} {B' : A' → Type ℓB'} {B'' : A'' → Type ℓB''}
  (f : I → A) (f' : I → A') (f'' : I → A'')
  (g1 : ∀ i → B (f i) → B' (f' i)) →
  (g2 : ∀ i → B' (f' i) → B'' (f'' i)) →
  ∀ is → mapOverSpan f f'' (λ i → g2 i ∘ g1 i) is ≡
          mapOverSpan {B = B'} {B' = B''} f' f'' g2 is ∘ mapOverSpan {B = B} f f' g1 is
mapOverSpan-∘ f f' f'' g1 g2 [] j [] = []
mapOverSpan-∘ {B' = B'} f f' f'' g1 g2 (i ∷ is) j (b ∷ bs) =
  g2 i (g1 i b) ∷ mapOverSpan-∘ {B' = B'} f f' f'' g1 g2 is j bs

mapOverSpan∘Idfun : ∀ {ℓI ℓA ℓA'' ℓB ℓB' ℓB''}
  {I : Type ℓI}
  {A : Type ℓA} {A'' : Type ℓA''}
  {B : A → Type ℓB} {B' : A → Type ℓB'} {B'' : A'' → Type ℓB''}
  (f' : I → A) (f'' : I → A'')
  (g1 : ∀ a → B a → B' a )
  (g2 : ∀ i → B' (f' i) → B'' (f'' i)) →
  ∀ is → mapOverSpan {B = B} {B' = B''} f' f'' (λ i → g2 i ∘ g1 (f' i)) is ≡
          mapOverSpan {B = B'} f' f'' g2 is ∘ mapOverIdfun g1 (map f' is)
mapOverSpan∘Idfun f' f'' g1 g2 [] j [] = []
mapOverSpan∘Idfun f' f'' g1 g2 (i ∷ is) j (b ∷ bs) =
  g2 i (g1 (f' i) b) ∷ mapOverSpan∘Idfun f' f'' g1 g2 is j bs
