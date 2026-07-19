module Cubical.Functions.Surjection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fixpoint

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT

private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  f : A → B

isSurjection : (A → B) → Type _
isSurjection f = ∀ b → ∥ fiber f b ∥₁

_↠_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↠ B = Σ[ f ∈ (A → B) ] isSurjection f

section→isSurjection : {g : B → A} → section f g → isSurjection f
section→isSurjection {g = g} s b = ∣ g b , s b ∣₁

isPropIsSurjection : isProp (isSurjection f)
isPropIsSurjection = isPropΠ λ _ → squash₁

isEquiv→isSurjection : isEquiv f → isSurjection f
isEquiv→isSurjection e b = ∣ fst (equiv-proof e b) ∣₁

isEquiv→isEmbedding×isSurjection : isEquiv f → isEmbedding f × isSurjection f
isEquiv→isEmbedding×isSurjection e = isEquiv→isEmbedding e , isEquiv→isSurjection e

isEmbedding×isSurjection→isEquiv : isEmbedding f × isSurjection f → isEquiv f
equiv-proof (isEmbedding×isSurjection→isEquiv {f = f} (emb , sur)) b =
  inhProp→isContr (PT.rec fib' (λ x → x) fib) fib'
  where
  hpf : hasPropFibers f
  hpf = isEmbedding→hasPropFibers emb

  fib : ∥ fiber f b ∥₁
  fib = sur b

  fib' : isProp (fiber f b)
  fib' = hpf b

isEquiv≃isEmbedding×isSurjection : isEquiv f ≃ isEmbedding f × isSurjection f
isEquiv≃isEmbedding×isSurjection = isoToEquiv (iso
  isEquiv→isEmbedding×isSurjection
  isEmbedding×isSurjection→isEquiv
  (λ _ → isOfHLevelΣ 1 isPropIsEmbedding (\ _ → isPropIsSurjection) _ _)
  (λ _ → isPropIsEquiv _ _ _))

-- obs: for epi⇒surjective to go through we require a stronger
-- hypothesis that one would expect:
-- f must cancel functions from a higher universe.
rightCancellable : (f : A → B) → Type _
rightCancellable {ℓ} {A} {ℓ'} {B} f = ∀ {C : Type (ℓ-suc (ℓ-max ℓ ℓ'))}
  → ∀ (g g' : B → C) → (∀ x → g (f x) ≡ g' (f x)) → ∀ y → g y ≡ g' y

-- This statement is in Mac Lane & Moerdijk (page 143, corollary 5).
epi⇒surjective : (f : A → B) → rightCancellable f → isSurjection f
epi⇒surjective f rc y = transport (fact₂ y) tt*
    where hasPreimage : (A → B) → B → _
          hasPreimage f y = ∥ fiber f y ∥₁

          fact₁ : ∀ x → Unit* ≡ hasPreimage f (f x)
          fact₁ x = hPropExt isPropUnit*
                             isPropPropTrunc
                             (λ _ → ∣ (x , refl) ∣₁)
                             (λ _ → tt*)

          fact₂ : ∀ y → Unit* ≡ hasPreimage f y
          fact₂ = rc _ _ fact₁

-- If h ∘ g is surjective, then h is surjective.
leftFactorSurjective : (g : A → B) (h : B → C)
                        → isSurjection (h ∘ g)
                        → isSurjection h
leftFactorSurjective g h sur-h∘g c = PT.rec isPropPropTrunc (λ (x , hgx≡c) → ∣ g x , hgx≡c ∣₁) (sur-h∘g c)

compSurjection : (f : A ↠ B) (g : B ↠ C)
                 → A ↠ C
compSurjection (f , sur-f) (g , sur-g) =
  (λ x → g (f x)) ,
   λ c → PT.rec isPropPropTrunc
                (λ (b , gb≡c) → PT.rec isPropPropTrunc (λ (a , fa≡b) → ∣ a , (cong g fa≡b ∙ gb≡c) ∣₁) (sur-f b))
                (sur-g c)

-- Lawvere's fixed point theorem
↠Fixpoint : ∀ {A : Type ℓ} {B : Type ℓ'}
           → (A ↠ (A → B))
           → (n : B → B)
           → ∥ Fixpoint n ∥₁
↠Fixpoint {A = A} {B = B} (f , surf) n
  = map (λ (a , fib) → g a , sym (cong n (funExt⁻ fib a))) (surf g)
  where g : A → B
        g a = n ( f a a )

-- Cantor's theorem, that no type surjects into its power set
¬Surjection-into-Powerset : ∀ {A : Type ℓ} → ¬ (A ↠ ℙ A)
¬Surjection-into-Powerset {A = A} (f , surf)
  = PT.rec isProp⊥ (λ (_ , fx≡g) → H₁ fx≡g (H₂ fx≡g (H₁ fx≡g))) (surf g)
  where _∉_ : ∀ {A} → A → ℙ A → Type ℓ
        x ∉ A = ¬ (x ∈ A)

        g : ℙ A
        g = λ x → (x ∉ f x , isProp¬ _)

        H₁ : {x : A} → f x ≡ g → x ∉ (f x)
        H₁ {x} fx≡g x∈fx = transport (cong (fst ∘ (_$ x)) fx≡g) x∈fx x∈fx

        H₂ : {x : A} → f x ≡ g → x ∉ (f x) → x ∈ (f x)
        H₂ {x} fx≡g x∈g = transport (cong (fst ∘ (_$ x)) (sym fx≡g)) x∈g
