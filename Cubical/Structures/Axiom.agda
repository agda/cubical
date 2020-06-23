{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Axiom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ : Level

-- Now, we want to add axioms (i.e. propositions) to our Structure S that don't affect the ι.
-- We use a lemma due to Zesen Qian, which can now be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83

AxiomStructure : (S : Type ℓ → Type ℓ₁)
                 (axioms : (X : Type ℓ) → S X → Type ℓ₂)
               → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
AxiomStructure S axioms X = Σ[ s ∈ S X ] (axioms X s)

AxiomIso : {S : Type ℓ → Type ℓ₁} (ι : StrIso S ℓ₁')
           (axioms : (X : Type ℓ) → S X → Type ℓ₂)
         → StrIso (AxiomStructure S axioms) ℓ₁'
AxiomIso ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

axiomUnivalentStr : {S : Type ℓ → Type ℓ₁}
                 (ι : (A B : Σ[ X ∈ (Type ℓ) ] (S X)) → A .fst ≃ B .fst → Type ℓ₁')
                 {axioms : (X : Type ℓ) → S X → Type ℓ₂}
                 (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
                 (θ : UnivalentStr S ι)
               → UnivalentStr (AxiomStructure S axioms) (AxiomIso ι axioms)
axiomUnivalentStr {S = S} ι {axioms = axioms} axioms-are-Props θ {X , s , a} {Y , t , b} f =
  compEquiv
    (θ f)
    (compEquiv
      (invEquiv (Σ-contractSnd λ _ → isOfHLevelPathP' 0 (λ _ → axioms-are-Props _ _) _ _))
      ΣPath≃PathΣ)

