{-# OPTIONS --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

{- Pointed functions -}
_→∙_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] f a ≡ b

_→∙_∙ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
(A →∙ B ∙) .fst = A →∙ B
(A →∙ B ∙) .snd .fst x = pt B
(A →∙ B ∙) .snd .snd = refl

idfun∙ : ∀ {ℓ} (A : Pointed ℓ) → A →∙ A
idfun∙ A .fst x = x
idfun∙ A .snd = refl

ua∙ : ∀ {ℓ} {A B : Pointed ℓ} (e : fst A ≃ fst B)
                  → fst e (snd A) ≡ snd B → A ≡ B
fst (ua∙ e p i) = ua e i
snd (ua∙ {A = A} e p i) = ua-gluePath e p i

{- J for pointed function types -}
→∙J : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Type ℓ'}
    → (P : (b₀ : B) (f : A →∙ (B , b₀)) → Type ℓ'')
    → ((f : fst A → B) → P (f (pt A)) (f , refl))
    → {b₀ : B} (f : A →∙ (B , b₀)) → P b₀ f
→∙J {A = A} P ind =
  uncurry λ f → J (λ b₀ y → P b₀ (f , y)) (ind f)

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
Pointer∙ A .fst = Pointer A
Pointer∙ A .snd = pt₀

Pointed≡∙Pointer : ∀ {ℓ} {A : Pointed ℓ} → A ≡ (Pointer A , pt₀)
Pointed≡∙Pointer {A = A} i = (Pointed≡Pointer {A = A} i) , helper i
  where
  helper : PathP (λ i → Pointed≡Pointer {A = A} i) (pt A) pt₀
  helper = ua-gluePath (isoToEquiv (IsoPointedPointer {A = A})) id

pointerFun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
            → Pointer A → Pointer B
pointerFun f pt₀ = pt₀
pointerFun f ⌊ x ⌋ = ⌊ fst f x ⌋
pointerFun f (id i) = (cong ⌊_⌋ (snd f) ∙ id) i

pointerFun∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
             → Pointer∙ A →∙ Pointer∙ B
pointerFun∙ f .fst = pointerFun f
pointerFun∙ f .snd = refl
