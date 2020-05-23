{-# OPTIONS --cubical --safe #-}
module Cubical.Homotopy.WedgeConnectivity where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
import Cubical.Data.NatMinusTwo as ℕ₋₂
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc
open import Cubical.Homotopy.Connected

module WedgeConnectivity {ℓ ℓ' ℓ''} (n m : ℕ)
  (A : Pointed ℓ) (connA : isHLevelConnected (suc n) (typ A))
  (B : Pointed ℓ') (connB : isHLevelConnected (suc m) (typ B))
  (P : typ A → typ B → HLevel ℓ'' (n + m))
  (f : (a : typ A) → P a (pt B) .fst)
  (g : (b : typ B) → P (pt A) b .fst)
  (p : f (pt A) ≡ g (pt B))
  where

  private
    Q : typ A → HLevel _ n
    Q a =
      ( (Σ[ k ∈ ((b : typ B) → P a b .fst) ] k (pt B) ≡ f a)
      , isOfHLevelRetract n
          (λ {(h , q) → h , funExt λ _ → q})
          (λ {(h , q) → h , funExt⁻ q _})
          (λ _ → refl)
          (isOfHLevelPrecomposeConnected n m (P a) (λ _ → pt B)
            (isHLevelConnectedPoint m connB (pt B)) (λ _ → f a))
      )

    main : isContr (fiber (λ s _ → s (pt A)) (λ _ → g , p ⁻¹))
    main =
      elim.isEquivPrecompose (λ _ → pt A) n Q
        (isHLevelConnectedPoint n connA (pt A))
        .equiv-proof (λ _ → g , p ⁻¹)

  abstract
    extension : ∀ a b → P a b .fst
    extension a b = main .fst .fst a .fst b

    left : ∀ a → extension a (pt B) ≡ f a
    left a = main .fst .fst a .snd

    right : ∀ b → extension (pt A) b ≡ g b
    right = funExt⁻ (cong fst (funExt⁻ (main .fst .snd) _))

    -- TODO: left (pt A) ⁻¹ ∙ right (pt B) ≡ p
