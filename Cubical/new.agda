{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.new where

open import Cubical.HITs.Rationals.HITQ.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import Cubical.Data.Int

open import Cubical.Data.Nat as ℕ hiding (_*_ ; +-comm) renaming (_+_ to _+n_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
_≤_ : Int → Int → Type₀
_≤_ a b = Σ[ x ∈ ℕ ] a + pos x ≡ b

almostHom : (f : Int → Int) → Type₀
almostHom f = Σ[ (max , min) ∈ Int × Int ] ((a b : Int) → (f (a + b) - ((f b) - f a)) ≤ max) × ((a b : Int) → min ≤ (f (a + b) - ((f b) - f a)))

_≡almost_ : (f g : Int → Int) → Type₀
_≡almost_ f g = Σ[ (max , min) ∈ Int × Int ] ((a : Int) → ((f a - g a) ≤ max) × (min ≤ (f a - g a)))

data R : Type₀ where
  r : (f : Int → Int) → R
  eq : (g h : (Int → Int)) → g ≡almost h → r g ≡ r h
  squashR : (a b : R) → (p q : a ≡ b) → p ≡ q
open import Cubical.HITs.Susp.Base
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation

data R→ (A : R → Type₀) : Type₀ where
  t : (r : R) (a : A r) → (R→ A)
  squash→ : (f g : Int → Int) → (f ≡almost g) → {!!}

isSetGenR : isSet R
isSetGenR = squashR

genR-ind : ∀{ℓ} {A : R → Type ℓ} → ((r : R) → isSet (A r)) → ((f : Int → Int) → A (r f)) → (r : R) → A r
genR-ind is-set ind (r f) = ind f
genR-ind is-set ind (eq g h p i) = {!ind h!}
genR-ind is-set ind (squashR x x₁ p q i i₁) = {!!}

funcGrAdd : {!!}
funcGrAdd = {!!}

-- funcGrAdd : genR → genR → R
-- funcGrAdd (r f) b = {!!}
-- funcGrAdd (eq g h x i) b = {!!}
-- funcGrAdd (higher g h p q i i₁) b = {!!}

-- -- funcGrAdd : genR → genR → genR
-- -- funcGrAdd (r f) (r g) = r λ x → f x + g x
-- -- funcGrAdd (r G) (eq f g p i) =
-- --   eq (λ x → G x + f x) (λ x → G x + g x) (fst p , (λ a → (fst (fst (snd p a)) , cong (_+ pos (fst (fst (snd p a)))) {!!} ∙ snd (fst (snd p a))) , {!!})) i 
-- -- funcGrAdd (eq f g x i) (r x₁) = {!!}
-- -- funcGrAdd (eq f g x i) (eq f₁ g₁ x₁ i₁) = {!!}

-- -- intHelper : (a b c : Int) → (a + b) - (a + c) ≡ b - c
-- -- intHelper (pos n) b c = {!+-comm!}
-- -- intHelper (negsuc n) b c = {!!}
-- -- intHelper2 : (a b c : Int) → (b + a) - (c + a) ≡ b - c
-- -- intHelper2 a b c = cong₂ (_-_) (+-comm b a) (+-comm c a) ∙ intHelper a b c


-- -- _+_→set : ∀{ℓ} {A : genR → Type ℓ} → ((r : genR) → isSet (A r)) → ((f : Int → Int) → A (r f)) → (r : genR) → A r 
-- -- (set + ind →set) (r f) = ind f
-- -- (set + ind →set) (eq g h x i) = {!x!}

-- -- _+r_ : R → R → R
-- -- _+r_ = elim2 (λ _ _ → setTruncIsSet) {!!}
-- --   where
-- --   +2 : (a b : genR) → R
-- --   +2 (r f) (r g) = ∣ r (λ x → f x + g x) ∣₂
-- --   +2 (r f) (eq g h p i) = ∣ eq (λ x → f x + g x)
-- --                               (λ x → f x + h x)
-- --                               (fst p
-- --                               , λ a → (fst (fst (snd p a))
-- --                                      , cong (_+ pos (fst (fst (snd p a)))) (intHelper (f a) (g a) (h a)) ∙ snd (fst (snd p a)))
-- --                                     , fst (snd (snd p a))
-- --                                      , snd (snd (snd p a)) ∙ sym (intHelper (f a) (g a) (h a))) i ∣₂
-- --   +2 (eq g h p i) (r f) = ∣ eq (λ x → g x + f x)
-- --                               (λ x → h x + f x)
-- --                               (fst p
-- --                               , λ a → (fst (fst (snd p a))
-- --                                      , cong (_+ pos (fst (fst (snd p a)))) (intHelper2 (f a) (g a) (h a)) ∙ snd (fst (snd p a)))
-- --                                     , fst (snd (snd p a))
-- --                                      , snd (snd (snd p a)) ∙ sym (intHelper2 (f a) (g a) (h a))) i ∣₂
-- --   +2 (eq f g p i) (eq f2 g2 p2 j) = {!!} -- setTruncIsSet ∣ eq (λ x → f x + f2 x) (λ x → g x + f2 x) ((fst (fst p) , snd (fst p)) , λ a → {!!}) i ∣₂ {!!} {!!} {!!} i j
