{- Basic definitions for the inductively defined equality type

- J, path composition, some laws for path composition, ap, transport

- equivalences

- equational reasoning combinators

-}

{-# OPTIONS --safe #-}

module Cubical.Data.Equality.Base where

open import Cubical.Foundations.Prelude public
  using (Type; Level; ℓ-zero; ℓ-suc; ℓ-max; Σ; Σ-syntax; _,_)
  renaming (fst to pr₁; snd to pr₂)

-- Import the builtin equality type defined as an inductive family
open import Agda.Builtin.Equality public

private
 variable
  a b ℓ ℓ' : Level
  A : Type a
  B : Type b
  x y z : A

J : (M : (y : A) (p : x ≡ y) → Type ℓ) → M x refl → (p : x ≡ y) → M y p
J M m refl = m

ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

infixr 30 _∙_
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infixr 2 step-≡
step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

syntax step-≡ x y p = x ≡⟨ p ⟩ y

infix  3 _∎
_∎ : (x : A) → x ≡ x
_ ∎ = refl

transport : ∀ (C : A → Type ℓ') {x y : A} → x ≡ y → C x → C y
transport C refl b = b

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

assoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl p q = refl

unitR : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
unitR refl = refl

invL :  {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
invL refl = refl

invR :  {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
invR refl = refl


transport-path : {x y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x) → transport (λ x → f x ≡ g x) p q ≡ sym (ap f p) ∙ q ∙ ap g p
transport-path f g refl q = sym (unitR q)

ap-∙ : {x y : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f refl q = refl

ap-const : {x y : A} (p : x ≡ y) (u : B) → ap (λ _ → u) p ≡ refl
ap-const refl _ = refl

sym-ap : (f : A → B) {x y : A} (p : x ≡ y) → sym (ap f p) ≡ ap f (sym p)
sym-ap f refl = refl

sym-invol : {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym-invol refl = refl

apd : {C : A → Type ℓ} (f : (x : A) → C x) {x y : A} (p : x ≡ y) → transport C p (f x) ≡ f y
apd f refl = refl


-- Equivalences expressed using ≡ everywhere
fiber : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

record isEquiv {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field equiv-proof : (y : B) → isContr (fiber f y)
open isEquiv public

infix 4 _≃_
_≃_ : ∀ (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : A ≃ B → A → B
equivFun e = e .pr₁

equivIsEquiv : (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = e .pr₂

equivCtr : (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .pr₂ .equiv-proof y .pr₁

id : A → A
id x = x

isEquivId : isEquiv (id {A = A})
equiv-proof isEquivId y = (y , refl) , λ where (_ , refl) → refl
