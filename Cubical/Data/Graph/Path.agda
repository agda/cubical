-- Paths in a graph
{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Data.Graph.Path where

open import Cubical.Data.Graph.Base
open import Cubical.Data.List.Base hiding (_++_)
open import Cubical.Foundations.Prelude hiding (Path)

module _ {ℓv ℓe : Level} (G : Graph ℓv ℓe) where
  data Path : (v w : Node G) → Type (ℓ-max ℓv ℓe) where
    pnil : ∀ {v} → Path v v
    pcons : ∀ {v w x} → Path v w → Edge G w x → Path v x

  -- Path concatenation
  ccat : ∀ {v w x} → Path v w → Path w x → Path v x
  ccat P pnil = P
  ccat P (pcons Q e) = pcons (ccat P Q) e

  private
    _++_ = ccat
    infixr 20 _++_

  -- Some properties
  pnil++ : ∀ {v w} (P : Path v w) → pnil ++ P ≡ P
  pnil++ pnil = refl
  pnil++ (pcons P e) = cong (λ P → pcons P e) (pnil++ _)
  
  ++assoc : ∀ {v w x y}
      (P : Path v w) (Q : Path w x) (R : Path x y)
    → (P ++ Q) ++ R ≡ P ++ (Q ++ R)
  ++assoc P Q pnil = refl
  ++assoc P Q (pcons R e) = cong (λ P → pcons P e) (++assoc P Q R)

  -- Paths as lists
  pathToList : ∀ {v w} → Path v w
      → List (Σ[ x ∈ Node G ] Σ[ y ∈ Node G ] Edge G x y)
  pathToList pnil = []
  pathToList (pcons P e) = (_ , _ , e) ∷ (pathToList P)

  isSetPath : ∀ v w → isSet (Path v w)
  isSetPath v w P Q eq1 eq2 = {!   !}
