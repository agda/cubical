-- We define ZigZag-complete relations and prove that bisimulations
-- give rise to equivalences on the set quotients.
{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.ZigZag.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties



private
 variable
  ℓ ℓ' : Level


isZigZagComplete : {A B : Type ℓ} (R : A → B → Type ℓ') → Type (ℓ-max ℓ ℓ')
isZigZagComplete R = ∀ a b a' b' → R a b → R a' b → R a' b' → R a b'


isBisimulation : {A B : Type ℓ} (R : A → B → Type ℓ') (f : A → B) (g : B → A) → Type (ℓ-max ℓ ℓ')
isBisimulation R f g =  isZigZagComplete R
                      × (∀ a → R a (f a))
                      × (∀ b → R (g b) b)


-- The following result is due to Carlo Angiuli
module Bisimulation→Equiv (A B : Type ℓ)
                          (R : A → B → Type ℓ')
                          (f : A → B) (g : B → A)
                          (isBisimRfg : isBisimulation R f g) where

 -- first we fix some notation
 zigzag : isZigZagComplete R
 zigzag = isBisimRfg .fst

 α : ∀ a → R a (f a)
 α = isBisimRfg .snd .fst

 β : ∀ b → R (g b) b
 β = isBisimRfg .snd .snd

 -- using R we can define binary relations on A and B
 Rᴬ : A → A → Type (ℓ-max ℓ ℓ')
 Rᴬ a a' = Σ[ b ∈ B ] (R a b × R a' b)

 Rᴮ : B → B → Type (ℓ-max ℓ ℓ')
 Rᴮ b b' = Σ[ a ∈ A ] (R a b × R a b')

 -- Rᴬ and Rᴮ are equivalence relations
 Rᴬ-reflexive : ∀ a → Rᴬ a a
 Rᴬ-reflexive a = f a , α a , α a

 Rᴬ-symmetric : ∀ a a' → Rᴬ a a' → Rᴬ a' a
 Rᴬ-symmetric a a' (b , r , s) = b , s , r

 Rᴬ-transitive : ∀ a a' a'' → Rᴬ a a' → Rᴬ a' a'' → Rᴬ a a''
 Rᴬ-transitive a a' a'' (b , r , s) (b' , r' , s') = b' , zigzag _ _ _ _ r s r' , s'


 Rᴮ-reflexive : ∀ b → Rᴮ b b
 Rᴮ-reflexive b = g b , β b , β b

 Rᴮ-symmetric : ∀ b b' → Rᴮ b b' → Rᴮ b' b
 Rᴮ-symmetric b b' (a , r , s) = a , s , r

 Rᴮ-transitive : ∀ b b' b'' → Rᴮ b b' → Rᴮ b' b'' → Rᴮ b b''
 Rᴮ-transitive b b' b'' (a , r , s) (a' , r' , s') = a , r , zigzag _ _ _ _ s r' s'


 -- proof of A / Rᴬ ≃ B / Rᴮ
 φ : A / Rᴬ → B / Rᴮ
 φ [ a ] = [ f a ]
 φ (eq/ a a' r i) = eq/ (f a) (f a') s i
  where
  s : Rᴮ (f a) (f a')
  s = a , α a , zigzag _ _ _ _ (r .snd .fst) (r .snd .snd) (α a')
 φ (squash/ x x₁ p q i j) = squash/ (φ x) (φ x₁) (cong φ p) (cong φ q) i j

 ψ : B / Rᴮ → A / Rᴬ
 ψ [ b ] = [ g b ]
 ψ (eq/ b b' s i) = eq/ (g b) (g b') r i
  where
  r : Rᴬ (g b) (g b')
  r = b' , zigzag _ _ _ _ (β b) (s .snd .fst) (s .snd .snd) , β b'
 ψ (squash/ y y₁ p q i j) =  squash/ (ψ y) (ψ y₁) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η y = elimProp (λ y → squash/ (φ (ψ y)) y) (λ b → eq/ _ _ (g b , α (g b) , β b)) y

 ε : retract φ ψ
 ε x = elimProp (λ x → squash/ (ψ (φ x)) x) (λ a → eq/ _ _ (f a , β (f a) , α a)) x

 Thm : (A / Rᴬ) ≃ (B / Rᴮ)
 Thm = isoToEquiv (iso φ ψ η ε)
