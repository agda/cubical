{-

In this file we apply the cubical machinery to Martin Hötzel-Escardó's
structure identity principle:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.SIP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence renaming (ua-pathToEquiv to ua-pathToEquiv')
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties renaming (cong≃ to _⋆_)
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sigma

open import Cubical.Foundations.Structure public

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    S : Type ℓ₁ → Type ℓ₂

-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
UnivalentStr-≡ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
UnivalentStr-≡ {ℓ₁} S ι = ∀ {X : Type ℓ₁} (s t : S X) → ι (X , s) (X , t) (idEquiv X) ≃ (s ≡ t)


-- We introduce the notation for structure preserving equivalences a
-- bit differently, but this definition doesn't actually change from
-- Escardó's notes.
_≃[_]_ : (A : TypeWithStr ℓ₁ S) (ι : StrIso S ℓ₂) (B : TypeWithStr ℓ₁ S) → Type (ℓ-max ℓ₁ ℓ₂)
A ≃[ ι ] B = Σ[ e ∈ typ A ≃ typ B ] (ι A B e)



-- The following PathP version of UnivalentStr-≡ is a bit easier to work with
-- for the proof of the SIP
UnivalentStr : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ₁) ℓ₂) ℓ₃)
UnivalentStr {ℓ₁} S ι = {A B : TypeWithStr ℓ₁ S} (e : typ A ≃ typ B)
                  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)

-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction UnivalentStr-≡→UnivalentStr corresponds more or less
-- to a dependent EquivJ formulation of Escardó's homomorphism-lemma.
UnivalentStr→UnivalentStr-≡ : (S : Type ℓ₁ → Type ℓ₂) (ι : StrIso S ℓ₃) → UnivalentStr S ι → UnivalentStr-≡ S ι
UnivalentStr→UnivalentStr-≡ S ι θ {X = X} s t = ι (X , s) (X , t) (idEquiv X)           ≃⟨ θ (idEquiv X) ⟩
                                   PathP (λ i → S (ua (idEquiv X) i)) s t  ≃⟨ φ ⟩
                                   s ≡ t                                   ■
  where
   φ = transportEquiv (λ j → PathP (λ i → S (uaIdEquiv {A = X} j i)) s t)


UnivalentStr-≡→UnivalentStr : (ι : StrIso S ℓ₃) → UnivalentStr-≡ S ι → UnivalentStr S ι
UnivalentStr-≡→UnivalentStr {S = S} ι θ {A = A} {B = B} e = EquivJ P C e (str A) (str B)
  where
   Y = typ B

   P : (X : Type _) → X ≃ Y → Type _
   P X e' = (s : S X) (t : S Y) → ι (X , s) (Y , t) e' ≃ PathP (λ i → S (ua e' i)) s t

   C : (s t : S Y) → ι (Y , s) (Y , t) (idEquiv Y) ≃ PathP (λ i → S (ua (idEquiv Y) i)) s t
   C s t = ι (Y , s) (Y , t) (idEquiv Y)           ≃⟨ θ s t ⟩
           s ≡ t                                   ≃⟨ ψ ⟩
           PathP (λ i → S (ua (idEquiv Y) i)) s t  ■
    where
     ψ = transportEquiv λ j → PathP (λ i → S (uaIdEquiv {A = Y} (~ j) i)) s t


--- We can now define an invertible function
---
---    sip : A ≃[ ι ] B → A ≡ B

module _ {S : Type ℓ₁ → Type ℓ₂} {ι : StrIso S ℓ₃}
  (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ₁ S)
  where

  sip : A ≃[ ι ] B → A ≡ B
  sip (e , p) i = ua e i , θ e .fst p i

  SIP : A ≃[ ι ] B ≃ (A ≡ B)
  SIP =
    sip , isoToIsEquiv (compIso (Σ-cong-iso (invIso univalenceIso) (equivToIso ∘ θ)) ΣPathIsoPathΣ)

  sip⁻ : A ≡ B → A ≃[ ι ] B
  sip⁻ = invEq SIP

-- Now, we want to join two structures. Together with the adding of
-- axioms this will allow us to prove that a lot of mathematical
-- structures are a standard notion of structure

join-structure : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
               → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
join-structure S₁ S₂ X = S₁ X × S₂ X


join-iso : {S₁ : Type ℓ₁ → Type ℓ₂} (ι₁ : StrIso S₁ ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄} (ι₂ : StrIso S₂ ℓ₅)
         → StrIso (join-structure S₁ S₂) (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)


join-SNS : {S₁ : Type ℓ₁ → Type ℓ₂} (ι₁ : StrIso S₁ ℓ₃) (θ₁ : UnivalentStr S₁ ι₁)
           {S₂ : Type ℓ₁ → Type ℓ₄} (ι₂ : StrIso S₂ ℓ₅) (θ₂ : UnivalentStr S₂ ι₂)
         → UnivalentStr (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS {S₁ = S₁} ι₁ θ₁ {S₂} ι₂ θ₂ {X , s₁ , s₂} {Y , t₁ , t₂} e = isoToEquiv (iso φ ψ η ε)
   where
    φ : join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e
      → PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
    φ (p , q) i = (θ₁ e .fst p i) , (θ₂ e .fst q i)

    ψ : PathP (λ i → join-structure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
      → join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e
    ψ p = invEq (θ₁ e) (λ i → p i .fst) , invEq (θ₂ e) (λ i → p i .snd)

    η : section φ ψ
    η p i j = retEq (θ₁ e) (λ k → p k .fst) i j , retEq (θ₂ e) (λ k → p k .snd) i j

    ε : retract φ ψ
    ε (p , q) i = secEq (θ₁ e) p i , secEq (θ₂ e) q i
