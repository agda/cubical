{-

Add axioms (i.e., propositions) to a structure S without changing the definition of structured equivalence.

X ↦ Σ[ s ∈ S X ] (P X s) where (P X s) is a proposition for all X and s.

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Axioms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ : Level

AxiomsStructure : (S : Type ℓ → Type ℓ₁)
  (axioms : (X : Type ℓ) → S X → Type ℓ₂)
  → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
AxiomsStructure S axioms X = Σ[ s ∈ S X ] (axioms X s)

AxiomsEquivStr : {S : Type ℓ → Type ℓ₁} (ι : StrEquiv S ℓ₁')
  (axioms : (X : Type ℓ) → S X → Type ℓ₂)
  → StrEquiv (AxiomsStructure S axioms) ℓ₁'
AxiomsEquivStr ι axioms (X , (s , a)) (Y , (t , b)) e = ι (X , s) (Y , t) e

axiomsUnivalentStr : {S : Type ℓ → Type ℓ₁}
  (ι : (A B : TypeWithStr ℓ S) → A .fst ≃ B .fst → Type ℓ₁')
  {axioms : (X : Type ℓ) → S X → Type ℓ₂}
  (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
  (θ : UnivalentStr S ι)
  → UnivalentStr (AxiomsStructure S axioms) (AxiomsEquivStr ι axioms)
axiomsUnivalentStr {S = S} ι {axioms = axioms} axioms-are-Props θ {X , s , a} {Y , t , b} e =
  ι (X , s) (Y , t) e
    ≃⟨ θ e ⟩
  PathP (λ i → S (ua e i)) s t
    ≃⟨ invEquiv (Σ-contractSnd λ _ → isOfHLevelPathP' 0 (axioms-are-Props _ _) _ _) ⟩
  Σ[ p ∈ PathP (λ i → S (ua e i)) s t ] PathP (λ i → axioms (ua e i) (p i)) a b
    ≃⟨ ΣPath≃PathΣ ⟩
  PathP (λ i → AxiomsStructure S axioms (ua e i)) (s , a) (t , b)
  ■

inducedStructure : {S : Type ℓ → Type ℓ₁}
  {ι : (A B : TypeWithStr ℓ S) → A .fst ≃ B .fst → Type ℓ₁'}
  (θ : UnivalentStr S ι)
  {axioms : (X : Type ℓ) → S X → Type ℓ₂}
  (A : TypeWithStr ℓ (AxiomsStructure S axioms)) (B : TypeWithStr ℓ S)
  → (typ A , str A .fst) ≃[ ι ] B
  → TypeWithStr ℓ (AxiomsStructure S axioms)
inducedStructure θ {axioms} A B eqv =
  B .fst , B .snd , subst (uncurry axioms) (sip θ _ _ eqv) (A .snd .snd)

transferAxioms : {S : Type ℓ → Type ℓ₁}
  {ι : (A B : TypeWithStr ℓ S) → A .fst ≃ B .fst → Type ℓ₁'}
  (θ : UnivalentStr S ι)
  {axioms : (X : Type ℓ) → S X → Type ℓ₂}
  (A : TypeWithStr ℓ (AxiomsStructure S axioms)) (B : TypeWithStr ℓ S)
  → (typ A , str A .fst) ≃[ ι ] B
  → axioms (fst B) (snd B)
transferAxioms θ {axioms} A B eqv =
  subst (uncurry axioms) (sip θ _ _ eqv) (A .snd .snd)
