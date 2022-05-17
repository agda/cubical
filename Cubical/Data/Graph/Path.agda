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


module _ {ℓv ℓe : Level} where

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
      PathWithLen 0 v w = Lift {j = ℓe} (v ≡ w)
      PathWithLen (suc n) v w = Σ[ k ∈ Node G ] (PathWithLen n v k × Edge G k w)

      isSetPathWithLen : ∀ n v w → isSet (PathWithLen n v w)
      isSetPathWithLen 0 _ _ = isOfHLevelLift 2 (isProp→isSet (isSetNode _ _))
      isSetPathWithLen (suc n) _ _ = isSetΣ isSetNode λ _ →
          isSet× (isSetPathWithLen _ _ _) (isSetEdge _ _)

      isSet-ΣnPathWithLen : ∀ {v w} → isSet (Σ[ n ∈ ℕ ] PathWithLen n v w)
      isSet-ΣnPathWithLen = isSetΣ isSetℕ (λ _ → isSetPathWithLen _ _ _)

      Path→PathWithLen : ∀ {v w} → Path v w → Σ[ n ∈ ℕ ] PathWithLen n v w
      Path→PathWithLen pnil = 0 , lift refl
      Path→PathWithLen (pcons P e) = suc (Path→PathWithLen P .fst) ,
                                          _ , Path→PathWithLen P .snd , e

      PathWithLen→Path : ∀ {v w} → Σ[ n ∈ ℕ ] PathWithLen n v w → Path v w
      PathWithLen→Path (0 , q) = subst (Path _) (q .lower) pnil
      PathWithLen→Path (suc n , _ , pwl , e) = pcons (PathWithLen→Path (n , pwl)) e

      Path→PWL→Path : ∀ {v w} P → PathWithLen→Path {v} {w} (Path→PathWithLen P) ≡ P
      Path→PWL→Path {v} pnil = substRefl {B = Path v} pnil
      Path→PWL→Path (pcons P x) = cong₂ pcons (Path→PWL→Path _) refl

      isSetPath : ∀ v w → isSet (Path v w)
      isSetPath v w = isSetRetract Path→PathWithLen PathWithLen→Path
                                   Path→PWL→Path isSet-ΣnPathWithLen
