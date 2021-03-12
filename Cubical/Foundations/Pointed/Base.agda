{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ′ : Level

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

{- Pointed functions -}
_→∙_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] f a ≡ b

_→∙_∙ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A →∙ B ∙  = (A →∙ B) , (λ x → pt B) , refl

idfun∙ : ∀ {ℓ} (A : Pointed ℓ) → A →∙ A
idfun∙ A = (λ x → x) , refl

{- HIT allowing for pattern matching on pointed types -}
data Pointer {ℓ} (A : Pointed ℓ) : Type ℓ where
  pt₀ : Pointer A
  ⌊_⌋ : typ A → Pointer A
  id : ⌊ pt A ⌋ ≡ pt₀

IsoPointedPointer : ∀ {ℓ} {A : Pointed ℓ} → Iso (typ A) (Pointer A)
Iso.fun IsoPointedPointer = ⌊_⌋
Iso.inv (IsoPointedPointer {A = A}) pt₀ = pt A
Iso.inv IsoPointedPointer ⌊ x ⌋ = x
Iso.inv (IsoPointedPointer {A = A}) (id i) = pt A
Iso.rightInv IsoPointedPointer pt₀ = id
Iso.rightInv IsoPointedPointer ⌊ x ⌋ = refl
Iso.rightInv IsoPointedPointer (id i) j = id (i ∧ j)
Iso.leftInv IsoPointedPointer x = refl

Pointed≡Pointer : ∀ {ℓ} {A : Pointed ℓ} → typ A ≡ Pointer A
Pointed≡Pointer = isoToPath IsoPointedPointer

Pointer∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
Pointer∙ A = Pointer A , pt₀

Pointed≡∙Pointer : ∀ {ℓ} {A : Pointed ℓ} → A ≡ (Pointer A , pt₀)
Pointed≡∙Pointer {A = A} i = (Pointed≡Pointer {A = A} i) , helper i
  where
  helper : PathP (λ i → Pointed≡Pointer {A = A} i) (pt A) pt₀
  helper = ua-gluePath (isoToEquiv (IsoPointedPointer {A = A})) id

pointerFun : {A : Pointed ℓ} {B : Pointed ℓ′} (f : A →∙ B)
            → Pointer A → Pointer B
pointerFun f pt₀ = pt₀
pointerFun f ⌊ x ⌋ = ⌊ fst f x ⌋
pointerFun f (id i) = (cong ⌊_⌋ (snd f) ∙ id) i

pointerFun∙ : {A : Pointed ℓ} {B : Pointed ℓ′} (f : A →∙ B)
             → Pointer∙ A →∙ Pointer∙ B
pointerFun∙ f = (pointerFun f) , refl

_≃∙_ : (A B : Pointed ℓ) → Type ℓ
A ≃∙ B = Σ[ f ∈ (fst A ≃ fst B) ] equivFun f (pt A) ≡ pt B

≃∙To→∙ : {A B : Pointed ℓ} → A ≃∙ B → (A →∙ B)
≃∙To→∙ ((f , _) , pointed) = f , pointed
