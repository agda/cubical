{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Core.Glue public
  using ( isEquiv ; equiv-proof ; _≃_ ; equivFun ; equivProof )

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to isContr (fiber f b).
strictContrFibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ[ t ∈ fiber f (f (g b)) ]
    ((t' : fiber f b) → Path (fiber f (f (g b))) t (g (f (t' .fst)) , cong (f ∘ g) (t' .snd)))
strictContrFibers {f = f} g b .fst = (g b , refl)
strictContrFibers {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

-- The identity equivalence
idIsEquiv : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
idIsEquiv A .equiv-proof = strictContrFibers (idfun A)

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

-- the definition using Π-type
isEquiv' : ∀ {ℓ}{ℓ'}{A : Type ℓ}{B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isEquiv' {B = B} f = (y : B) → isContr (fiber f y)
