module Cubical.Categories.Site.Sieve where

-- Definition of sieves on an object
-- and the sieve generated by a cover.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

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
      passes : {d : ob} → Hom[ d , c ] → Type ℓsie
      isPropPasses : {d : ob} → (f : Hom[ d , c ]) → isProp (passes f)
      closedUnderPrecomposition :
        {d' d : ob} (p : Hom[ d' , d ]) (f : Hom[ d , c ]) →
        passes f → passes (p ⋆ f)


module _
  {ℓ ℓ' : Level}
  {C : Category ℓ ℓ'}
  where

  open Category C hiding (_∘_)
  open Sieve

  sieveRefinesSieve :
    {ℓS' ℓS : Level} →
    {c : ob} →
    Sieve C ℓS' c →
    Sieve C ℓS c →
    Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓS') ℓS)
  sieveRefinesSieve S' S =
    (d : ob) →
    (f : Hom[ d , _ ]) →
    passes S' f → passes S f

  isPropSieveRefinesSieve :
    {ℓS' ℓS : Level} →
    {c : ob} →
    (S : Sieve C ℓS' c) →
    (S' : Sieve C ℓS c) →
    isProp (sieveRefinesSieve S S')
  isPropSieveRefinesSieve S S' =
    isPropΠ3 (λ d f _ → isPropPasses S' f)

  generatedSieve : {ℓ : Level} {c : ob} → Cover C ℓ c → Sieve C (ℓ-max ℓ' ℓ) c
  passes (generatedSieve cov) f =
    ∃[ i ∈ ⟨ cov ⟩ ] Σ[ h ∈ Hom[ _ , _ ] ] f ≡ h ⋆ patchArr cov i
  isPropPasses (generatedSieve cov) f = isPropPropTrunc
  closedUnderPrecomposition (generatedSieve cov) p f =
    PT.rec isPropPropTrunc λ (i , h , f≡hi) →
      ∣   i
        , (p ⋆ h)
        , ( (p ⋆ f)                     ≡⟨ cong (p ⋆_) f≡hi ⟩
            (p ⋆ (h ⋆ patchArr cov i))  ≡⟨ sym (⋆Assoc p h (patchArr cov i)) ⟩
            ((p ⋆ h) ⋆ patchArr cov i)  ∎ )
      ∣₁

  coverRefinesSieve :
    {ℓcov ℓsie : Level}
    {c : ob} →
    Cover C ℓcov c →
    Sieve C ℓsie c →
    Type (ℓ-max ℓcov ℓsie)
  coverRefinesSieve cov S =
    (i : _) → passes S (patchArr cov i)

  isPropCoverRefinesSieve :
    {ℓcov ℓsie : Level}
    {c : ob} →
    (cov : Cover C ℓcov c) →
    (S : Sieve C ℓsie c) →
    isProp (coverRefinesSieve cov S)
  isPropCoverRefinesSieve _ S = isPropΠ (λ _ → isPropPasses S _)

  coverRefinesGeneratedSieve :
    {ℓ : Level} →
    {c : ob} →
    {cov : Cover C ℓ c} →
    coverRefinesSieve cov (generatedSieve cov)
  coverRefinesGeneratedSieve i = ∣ i , id , sym (⋆IdL _) ∣₁

  -- The universal property of generatedSieve
  generatedSieveIsUniversal :
    {ℓcov ℓsie : Level} →
    {c : ob} →
    (cov : Cover C ℓcov c) →
    (S : Sieve C ℓsie c) →
    coverRefinesSieve cov S →
    sieveRefinesSieve (generatedSieve cov) S
  generatedSieveIsUniversal cov S cov≤S d f =
    PT.rec (isPropPasses S f) (λ (i , g , eq) →
      subst (passes S) (sym eq)
        (closedUnderPrecomposition S g (patchArr cov i) (cov≤S i)) )

  pulledBackSieve :
    {ℓsie : Level} →
    {c d : ob} →
    (Hom[ c , d ]) →
    Sieve C ℓsie d →
    Sieve C ℓsie c
  passes (pulledBackSieve f S) g = passes S (g ⋆ f)
  isPropPasses (pulledBackSieve f S) g = isPropPasses S _
  closedUnderPrecomposition (pulledBackSieve f S) p g pass =
    subst (passes S) (sym (⋆Assoc p g f))
      (closedUnderPrecomposition S p (g ⋆ f) pass)
