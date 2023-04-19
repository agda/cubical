{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sieve where

-- Definition of sieves on an object
-- and the generated sieve of a cover.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic using (∀[]-syntax)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover

module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category C

  record Sieve (ℓsie : Level) (c : ob) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓsie))) where
    no-eta-equality
    field
      passes : {d : ob} → Hom[ d , c ] → hProp ℓsie
      closedUnderPrecomposition :
        {d' d : ob} (p : Hom[ d' , d ]) (f : Hom[ d , c ]) →
        ⟨ passes f ⟩ → ⟨ passes (p ⋆ f) ⟩

  open Sieve

  generatedSieve : {ℓ : Level} {c : ob} → Cover C ℓ c → Sieve (ℓ-max ℓ' ℓ) c
  passes (generatedSieve cov) f =
      (∃[ i ∈ ⟨ cov ⟩ ] ∃[ h ∈ Hom[ _ , _ ] ] f ≡ h ⋆ patchArr C cov i)
    , isPropPropTrunc
  closedUnderPrecomposition (generatedSieve cov) p f =
    PT.rec isPropPropTrunc (uncurry λ i → PT.map λ (h , f≡hi) →
        i
      , ∣ (p ⋆ h) ,
          ( (p ⋆ f)                ≡⟨ cong (p ⋆_) f≡hi ⟩
            (p ⋆ (h ⋆ patchArr C cov i)) ≡⟨ sym (⋆Assoc p h (patchArr C cov i)) ⟩
            ((p ⋆ h) ⋆ patchArr C cov i) ∎ )
        ∣₁ )

  coverRefinesSieve :
    {ℓcov ℓsie : Level}
    {c : ob} →
    Cover C ℓcov c →
    Sieve ℓsie c →
    hProp (ℓ-max ℓcov ℓsie)
  coverRefinesSieve cov S =
    ∀[ i ] passes S (patchArr C cov i)

  -- TODO: prove universal property of generatedSieve

  -- pulledBackSieve :
