-- Paths in a graph

module Cubical.Data.Graph.Path where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (Path)

open import Cubical.Data.Graph.Base
open import Cubical.Data.List.Base hiding (_++_; map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma.Base hiding (Path)

private variable
  ℓv ℓe ℓv' ℓe'  : Level

module _ (G : Graph ℓv ℓe) where
  data Path : (v w : Node G) → Type (ℓ-max ℓv ℓe) where
    pnil : ∀ {v} → Path v v
    pcons : ∀ {v x w} → Edge G v x → Path x w → Path v w

module _ {G : Graph ℓv ℓe} where

  -- Path concatenation
  ccat : ∀ {v x w} → Path G v x → Path G x w → Path G v w
  ccat pnil Q = Q
  ccat (pcons e P) Q = pcons e (ccat P Q)

  _++_ = ccat
  infixr 20 _++_

  -- Some properties
  pnil++ : ∀ {v w} (P : Path G v w) → pnil ++ P ≡ P
  pnil++ pnil = refl
  pnil++ (pcons e P) = cong (λ P → pcons e P) (pnil++ _)

  ++pnil : ∀ {v w} (P : Path G v w) → P ++ pnil ≡ P
  ++pnil pnil = refl
  ++pnil (pcons e P) = cong (λ P → pcons e P) (++pnil P)

  ++assoc : ∀ {v w x y}
      (P : Path G v w) (Q : Path G w x) (R : Path G x y)
    → (P ++ Q) ++ R ≡ P ++ (Q ++ R)
  ++assoc pnil P Q = refl
  ++assoc (pcons e P) Q R = cong (λ P → pcons e P) (++assoc P Q R)

  -- Paths as lists
  pathToList : ∀ {v w} → Path G v w
      → List (Σ[ x ∈ Node G ] Σ[ y ∈ Node G ] Edge G x y)
  pathToList pnil = []
  pathToList (pcons e P) = (_ , _ , e) ∷ (pathToList P)

  -- Path v w is a set
  -- Lemma 4.2 of https://arxiv.org/abs/2112.06609
  module _ (isSetNode : isSet (Node G))
           (isSetEdge : ∀ v w → isSet (Edge G v w)) where

    -- This is called ̂W (W-hat) in the paper
    PathWithLen : ℕ → Node G → Node G → Type (ℓ-max ℓv ℓe)
    PathWithLen 0 v w = Lift {j = ℓe} (v ≡ w)
    PathWithLen (suc n) v w = Σ[ x ∈ Node G ] (Edge G v x × PathWithLen n x w)

    isSetPathWithLen : ∀ n v w → isSet (PathWithLen n v w)
    isSetPathWithLen 0 _ _ = isOfHLevelLift 2 (isProp→isSet (isSetNode _ _))
    isSetPathWithLen (suc n) _ _ = isSetΣ isSetNode λ _ →
        isSet× (isSetEdge _ _) (isSetPathWithLen _ _ _)

    isSet-ΣnPathWithLen : ∀ {v w} → isSet (Σ[ n ∈ ℕ ] PathWithLen n v w)
    isSet-ΣnPathWithLen = isSetΣ isSetℕ (λ _ → isSetPathWithLen _ _ _)

    Path→PathWithLen : ∀ {v w} → Path G v w → Σ[ n ∈ ℕ ] PathWithLen n v w
    Path→PathWithLen pnil = 0 , lift refl
    Path→PathWithLen (pcons e P) = suc (Path→PathWithLen P .fst) , _ , e , Path→PathWithLen P .snd

    PathWithLen→Path : ∀ {v w} → Σ[ n ∈ ℕ ] PathWithLen n v w → Path G v w
    PathWithLen→Path (0 , q) = subst (Path G _) (q .lower) pnil
    PathWithLen→Path (suc n , _ , e , pwl) = pcons e (PathWithLen→Path (n , pwl))

    Path→PWL→Path : ∀ {v w} P → PathWithLen→Path {v} {w} (Path→PathWithLen P) ≡ P
    Path→PWL→Path {v} pnil = substRefl {B = Path G v} pnil
    Path→PWL→Path (pcons P x) = cong₂ pcons refl (Path→PWL→Path _)

    isSetPath : ∀ v w → isSet (Path G v w)
    isSetPath v w = isSetRetract Path→PathWithLen PathWithLen→Path
                                 Path→PWL→Path isSet-ΣnPathWithLen

module _ {G : Graph ℓv ℓe} {H : Graph ℓv' ℓe'} where
  open GraphHom
  map : {x y : Node G}
        (F : GraphHom G H)
        → Path G x y → Path H (F $g x) (F $g y)
  map F pnil = pnil
  map F (pcons e p) = pcons (F <$g> e) (map F p)

  map++ : {x y z : Node G}
        (F : GraphHom G H)
        → (p : Path G x y) → (q : Path G y z)
        → map F (p ++ q) ≡ map F p ++ map F q
  map++ F pnil q = refl
  map++ F (pcons x p) q = cong (λ m → pcons (F <$g> x) m) (map++ F p q)
