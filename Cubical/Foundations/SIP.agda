{-

In this file we apply the cubical machinery to Martin Hötzel-Escardó's
structure identity principle:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence renaming (ua-pathToEquiv to ua-pathToEquiv')
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Foundations.Structure public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    S : Type ℓ₁ → Type ℓ₂

-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
SNS : (S : Type ℓ₁ → Type ℓ₂) (ι : StrEquiv S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
SNS {ℓ₁} S ι = ∀ {X : Type ℓ₁} (s t : S X) → ι (X , s) (X , t) (idEquiv X) ≃ (s ≡ t)

-- We introduce the notation for structure preserving equivalences a
-- bit differently, but this definition doesn't actually change from
-- Escardó's notes.
_≃[_]_ : (A : TypeWithStr ℓ₁ S) (ι : StrEquiv S ℓ₂) (B : TypeWithStr ℓ₁ S) → Type (ℓ-max ℓ₁ ℓ₂)
A ≃[ ι ] B = Σ[ e ∈ typ A ≃ typ B ] (ι A B e)



-- The following PathP version of SNS is a bit easier to work with
-- for the proof of the SIP
UnivalentStr : (S : Type ℓ₁ → Type ℓ₂) (ι : StrEquiv S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
UnivalentStr {ℓ₁} S ι =
  {A B : TypeWithStr ℓ₁ S} (e : typ A ≃ typ B)
  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction SNS→UnivalentStr corresponds more or less
-- to a dependent EquivJ formulation of Escardó's homomorphism-lemma.
UnivalentStr→SNS : (S : Type ℓ₁ → Type ℓ₂) (ι : StrEquiv S ℓ₃)
  → UnivalentStr S ι → SNS S ι
UnivalentStr→SNS S ι θ {X = X} s t =
  ι (X , s) (X , t) (idEquiv X)
    ≃⟨ θ (idEquiv X) ⟩
  PathP (λ i → S (ua (idEquiv X) i)) s t
    ≃⟨ transportEquiv (λ j → PathP (λ i → S (uaIdEquiv {A = X} j i)) s t) ⟩
  s ≡ t
  ■


SNS→UnivalentStr : (ι : StrEquiv S ℓ₃) → SNS S ι → UnivalentStr S ι
SNS→UnivalentStr {S = S} ι θ {A = A} {B = B} e = EquivJ P C e (str A) (str B)
  where
  Y = typ B

  P : (X : Type _) → X ≃ Y → Type _
  P X e' = (s : S X) (t : S Y) → ι (X , s) (Y , t) e' ≃ PathP (λ i → S (ua e' i)) s t

  C : (s t : S Y) → ι (Y , s) (Y , t) (idEquiv Y) ≃ PathP (λ i → S (ua (idEquiv Y) i)) s t
  C s t =
    ι (Y , s) (Y , t) (idEquiv Y)
      ≃⟨ θ s t ⟩
    s ≡ t
      ≃⟨ transportEquiv (λ j → PathP (λ i → S (uaIdEquiv {A = Y} (~ j) i)) s t) ⟩
    PathP (λ i → S (ua (idEquiv Y) i)) s t
    ■

TransportStr : {S : Type ℓ → Type ℓ₁} (α : EquivAction S) → Type (ℓ-max (ℓ-suc ℓ) ℓ₁)
TransportStr {ℓ} {S = S} α =
  {X Y : Type ℓ} (e : X ≃ Y) (s : S X) → equivFun (α e) s ≡ subst S (ua e) s

TransportStr→UnivalentStr : {S : Type ℓ → Type ℓ₁} (α : EquivAction S)
  → TransportStr α → UnivalentStr S (EquivAction→StrEquiv α)
TransportStr→UnivalentStr {S = S} α τ {X , s} {Y , t} e =
  equivFun (α e) s ≡ t
    ≃⟨ pathToEquiv (cong (_≡ t) (τ e s)) ⟩
  subst S (ua e) s ≡ t
    ≃⟨ invEquiv (PathP≃Path _ _ _) ⟩
  PathP (λ i → S (ua e i)) s t
  ■

UnivalentStr→TransportStr : {S : Type ℓ → Type ℓ₁} (α : EquivAction S)
  → UnivalentStr S (EquivAction→StrEquiv α) → TransportStr α
UnivalentStr→TransportStr {S = S} α θ e s =
  invEq (θ e) (transport-filler (cong S (ua e)) s)

invTransportStr : {S : Type ℓ → Type ℓ₂} (α : EquivAction S) (τ : TransportStr α)
  {X Y : Type ℓ} (e : X ≃ Y) (t : S Y) → invEq (α e) t ≡ subst⁻ S (ua e) t
invTransportStr {S = S} α τ e t =
  sym (transport⁻Transport (cong S (ua e)) (invEq (α e) t))
  ∙∙ sym (cong (subst⁻ S (ua e)) (τ e (invEq (α e) t)))
  ∙∙ cong (subst⁻ S (ua e)) (secEq (α e) t)


--- We can now define an invertible function
---
---    sip : A ≃[ ι ] B → A ≡ B

module _ {S : Type ℓ₁ → Type ℓ₂} {ι : StrEquiv S ℓ₃}
  (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ₁ S)
  where

  sip : A ≃[ ι ] B → A ≡ B
  sip (e , p) i = ua e i , θ e .fst p i

  SIP : A ≃[ ι ] B ≃ (A ≡ B)
  SIP =
    sip , isoToIsEquiv (compIso (Σ-cong-iso (invIso univalenceIso) (equivToIso ∘ θ)) ΣPathIsoPathΣ)

  sip⁻ : A ≡ B → A ≃[ ι ] B
  sip⁻ = invEq SIP
