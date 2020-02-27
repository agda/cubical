{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Structure.SNS where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties renaming (cong≃ to _⋆_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Foundations.Structure.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'


-- Note that for any equivalence (f , e) : X ≃ Y the type  ι (X , s) (Y , t) (f , e) need not to be
-- a proposition. Indeed this type should correspond to the ways s and t can be identified
-- as S-structures. This we call a standard notion of structure or SNS.
-- We will use a different definition, but the two definitions are interchangeable.
SNS₁ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₁ {ℓ} S ι = ∀ {X : Type ℓ} (s t : S X) → ((s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X))


-- We introduce the notation for structure preserving equivalences a bit differently,
-- but this definition doesn't actually change from Escardó's notes.
_≃[_]_ : (A : TypeWithStr ℓ S) (ι : StrIso S ℓ') (B : TypeWithStr ℓ S) → Type (ℓ-max ℓ ℓ')
A ≃[ ι ] B = Σ[ f ∈ (typ A ≃ typ B) ] (ι A B f)


-- Our new definition of standard notion of structure SNS₂ using the ⋆ notation.
-- This is easier to work with than SNS₁ wrt Glue-types
SNS₂ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₂ {ℓ} S ι = (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B)
             → (equivFun (S ⋆ e) (str A) ≡ (str B)) ≃ (ι A B e)

-- We can unfold SNS₂ as follows:
SNS₃ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₃ {ℓ} S ι = (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B)
             → (transport (λ i → S (ua e i)) (str A) ≡ (str B)) ≃ (ι A B e)

SNS₂≡SNS₃ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₂ S ι ≡ SNS₃ S ι
SNS₂≡SNS₃ S ι = refl


-- A quick sanity-check that our definition is interchangeable with
-- Escardó's. The direction SNS₁→SNS₂ corresponds more or less to an
-- EquivJ formulation of Escardó's homomorphism-lemma.
SNS₂→SNS₁ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₂ S ι → SNS₁ S ι
SNS₂→SNS₁ S ι θ {X = X} s t =
  subst (λ e → (equivFun e s ≡ t) ≃ ι (X , s) (X , t) (idEquiv X)) (cong≃-idEquiv S X) θ-id
  where
   θ-id = θ (X , s) (X , t) (idEquiv X)

SNS₁→SNS₂ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₁ S ι → SNS₂ S ι
SNS₁→SNS₂ S ι θ A B e = EquivJ P C (typ B) (typ A) e (str B) (str A)
  where
   P : (X Y : Type _) → Y ≃ X → Type _
   P X Y e' = (s : S X) (t : S Y) → (equivFun (S ⋆ e') t ≡ s) ≃ ι (Y , t) (X , s) e'

   C : (X : Type _) → (s t : S X) → (equivFun (S ⋆ (idEquiv X)) t ≡ s) ≃ ι (X , t) (X , s) (idEquiv X)
   C X s t = subst (λ u →  (u ≡ s) ≃ (ι (X , t) (X , s) (idEquiv X)))
                   (sym ( cong (λ f → (equivFun f) t) (cong≃-idEquiv S X))) (θ t s)


-- The following PathP (i.e. transport-free) version of SNS₃ is a bit easier to
-- work with for the proof of the SIP
SNS₄ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
SNS₄ {ℓ} S ι = (A B : TypeWithStr ℓ S) (e : typ A ≃ typ B)
             → (PathP (λ i → S (ua e i)) (str A) (str B)) ≃ (ι A B e)

-- We can easily go between SNS₃ (which is def. equal to SNS₂) and SNS₄
-- We should be able to find are more direct version of PathP≃Path for the family (λ i → S (ua f i))
-- using glue and unglue terms.
SNS₂→SNS₄ : {S : Type ℓ → Type ℓ'} {ι : StrIso S ℓ''} → SNS₂ S ι → SNS₄ S ι
SNS₂→SNS₄ {S = S} h A B f =  PathP (λ i → S (ua f i)) (str A) (str B)
                          ≃⟨ PathP≃Path (λ i → S (ua f i)) (str A) (str B) ⟩
                             h A B f

SNS₄→SNS₂ : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'') → SNS₄ S ι → SNS₂ S ι
SNS₄→SNS₂ S ι h A B f =  transport (λ i → S (ua f i)) (str A) ≡ (str B)
                      ≃⟨ invEquiv (PathP≃Path (λ i → S (ua f i)) (str A) (str B)) ⟩
                         h A B f
