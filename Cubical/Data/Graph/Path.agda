-- Paths in a graph
{-# OPTIONS --safe #-}

module Cubical.Data.Graph.Path where

open import Cubical.Data.Graph.Base
open import Cubical.Data.List.Base hiding (_++_)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma.Base hiding (Path)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (Path)

private
  variable
    ℓv : Level

ℓe = ℓv

module _ (G : Graph ℓv ℓe) where
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

  -- Path v w is a set
  -- Lemma 4.2 of https://arxiv.org/abs/2112.06609
  module _ (isSetNode : isSet (Node G))
           (isSetEdge : ∀ v w → isSet (Edge G v w)) where

    -- This is called ̂W (W-hat) in the paper
    PathWithLen : ℕ → Node G → Node G → Type (ℓ-max ℓv ℓe)
    PathWithLen 0 v w = (v ≡ w)
    PathWithLen (suc n) v w = Σ[ k ∈ Node G ] (Edge G v k × PathWithLen n k w)

    isSetPathWithLen : ∀ n v w → isSet (PathWithLen n v w)
    isSetPathWithLen 0 v w = isProp→isSet (isSetNode _ _)
    isSetPathWithLen (suc n) v w = isSetΣ isSetNode λ _ →
        isSet× (isSetEdge _ _) (isSetPathWithLen _ _ _)

    module _ (v w : Node G) where
      isSet-ΣnPathWithLen : isSet (Σ[ n ∈ ℕ ] PathWithLen n v w)
      isSet-ΣnPathWithLen = isSetΣ isSetℕ (λ _ → isSetPathWithLen _ _ _)

      Path→PathWithLen : Path v w → Σ[ n ∈ ℕ ] PathWithLen n v w
      Path→PathWithLen pnil = ( 0 , refl )
      Path→PathWithLen (pcons P e) = fst (Path→PathWithLen P)
                              , (e , snd (Path→PathWithLen P))

      PathWithLen→Path : Σ[ n ∈ ℕ ] PathWithLen n v w → Path v w
      PathWithLen→Path = {!   !}

      Path→PWL→Path : ∀ x → PathWithLen→Path (Path→PathWithLen P) ≡ P
      Path→PWL→Path = {!   !}

      isSetPath : isSet (Path v w)
      isSetPath = isSetRetract Path→PathWithLen PathWithLen→Path
                               Path→PWL→Path isSet-ΣnPathWithLen
