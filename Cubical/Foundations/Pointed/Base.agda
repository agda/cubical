module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

Lift∙ : ∀ {i j} → (A : Pointed i) → Pointed (ℓ-max i j)
fst (Lift∙ {j = j} A) = Lift {j = j} (typ A)
snd (Lift∙ A) = lift (pt A)

{- Pointed functions -}
_→∙_ : (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] f a ≡ b

_→∙_∙ : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
(A →∙ B ∙) .fst = A →∙ B
(A →∙ B ∙) .snd .fst x = pt B
(A →∙ B ∙) .snd .snd = refl

idfun∙ : (A : Pointed ℓ) → A →∙ A
idfun∙ A .fst x = x
idfun∙ A .snd = refl

infix 3 _≃∙_
{-Pointed equivalences -}
_≃∙_ : (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
A ≃∙ B = Σ[ e ∈ fst A ≃ fst B ] fst e (pt A) ≡ pt B

{- Underlying pointed map of an equivalence -}
≃∙map : {A : Pointed ℓ} {B : Pointed ℓ'} → A ≃∙ B → A →∙ B
fst (≃∙map e) = fst (fst e)
snd (≃∙map e) = snd e

invEquiv∙ : {A : Pointed ℓ} {B : Pointed ℓ'} → A ≃∙ B → B ≃∙ A
fst (invEquiv∙ x) = invEquiv (fst x)
snd (invEquiv∙ {A = A} x) =
  sym (cong (fst (invEquiv (fst x))) (snd x)) ∙ retEq (fst x) (pt A)

compEquiv∙ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → A ≃∙ B → B ≃∙ C → A ≃∙ C
fst (compEquiv∙ e1 e2) = compEquiv (fst e1) (fst e2)
snd (compEquiv∙ e1 e2) = cong (fst (fst e2)) (snd e1) ∙ snd e2

Equiv∙J : {B : Pointed ℓ} (C : (A : Pointed ℓ) → A ≃∙ B → Type ℓ')
          → C B (idEquiv (fst B) , refl)
          → {A : _} (e : A ≃∙ B) → C A e
Equiv∙J {ℓ} {ℓ'} {B = B} C ind {A = A} =
  uncurry λ e p → help e (pt A) (pt B) p C ind
  where
  help : ∀ {A : Type ℓ} (e : A ≃ typ B) (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p)
  help = EquivJ (λ A e → (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p))
        λ a b → J (λ b p
          → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
                → C (fst B , b)
      (idEquiv (fst B) , refl) →
      C (typ B , a) (idEquiv (typ B) , p))
         λ _ p → p

ua∙ : {A B : Pointed ℓ} (e : fst A ≃ fst B)
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

IsoPointedPointer : {A : Pointed ℓ} → Iso (typ A) (Pointer A)
Iso.fun IsoPointedPointer = ⌊_⌋
Iso.inv (IsoPointedPointer {A = A}) pt₀ = pt A
Iso.inv IsoPointedPointer ⌊ x ⌋ = x
Iso.inv (IsoPointedPointer {A = A}) (id i) = pt A
Iso.rightInv IsoPointedPointer pt₀ = id
Iso.rightInv IsoPointedPointer ⌊ x ⌋ = refl
Iso.rightInv IsoPointedPointer (id i) j = id (i ∧ j)
Iso.leftInv IsoPointedPointer x = refl

Pointed≡Pointer : {A : Pointed ℓ} → typ A ≡ Pointer A
Pointed≡Pointer = isoToPath IsoPointedPointer

Pointer∙ : (A : Pointed ℓ) → Pointed ℓ
Pointer∙ A .fst = Pointer A
Pointer∙ A .snd = pt₀

Pointed≡∙Pointer : {A : Pointed ℓ} → A ≡ (Pointer A , pt₀)
Pointed≡∙Pointer {A = A} i = (Pointed≡Pointer {A = A} i) , helper i
  where
  helper : PathP (λ i → Pointed≡Pointer {A = A} i) (pt A) pt₀
  helper = ua-gluePath (isoToEquiv (IsoPointedPointer {A = A})) id

pointerFun : ∀ {ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
            → Pointer A → Pointer B
pointerFun f pt₀ = pt₀
pointerFun f ⌊ x ⌋ = ⌊ fst f x ⌋
pointerFun f (id i) = (cong ⌊_⌋ (snd f) ∙ id) i

pointerFun∙ : ∀ {ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
             → Pointer∙ A →∙ Pointer∙ B
pointerFun∙ f .fst = pointerFun f
pointerFun∙ f .snd = refl


-- pointed identity equivalence
idEquiv∙ : (A : Pointed ℓ) → (A ≃∙ A)
idEquiv∙ A = idEquiv (typ A) , refl

{-
  Equational reasoning for pointed equivalences
-}

infix  3 _∎≃∙
infixr 2 _≃∙⟨_⟩_

_∎≃∙ : (A : Pointed ℓ) → A ≃∙ A
A ∎≃∙ = idEquiv∙ A

_≃∙⟨_⟩_ : {B C : Pointed ℓ} (A : Pointed ℓ) → A ≃∙ B → B ≃∙ C → A ≃∙ C
A ≃∙⟨ f ⟩ g = compEquiv∙ f g
