{-# OPTIONS --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.itree where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.Coalg

-- Delay monad defined as an M-type
delay-S : (R : Type₀) -> Container ℓ-zero
delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Type₀) -> Type₀
delay R = M (delay-S R)

delay-ret : {R : Type₀} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Type₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

-- Bottom element raised
data ⊥₁ : Type₁ where

-- TREES
tree-S : (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
tree-S E R = (R ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

tree : (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
tree E R = M (tree-S E R)

tree-ret : ∀ {E} {R}  -> R -> tree E R
tree-ret {E} {R} r = in-fun (inl r , λ ())

tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

-- ITrees (and buildup examples)
-- https://arxiv.org/pdf/1906.00046.pdf
-- Interaction Trees: Representing Recursive and Impure Programs in Coq
-- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, Steve Zdancewic

itree-S : ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
itree-S E R = ((Unit ⊎ R) ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

itree :  ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
itree E R = M (itree-S E R)

ret' : ∀ {E} {R}  -> R -> P₀ (itree-S E R) (itree E R)
ret' {E} {R} r = inl (inr r) , λ ()

tau' : {E : Type₀ -> Type₁} -> {R : Type₀} -> itree E R -> P₀ (itree-S E R) (itree E R)
tau' t = inl (inl tt) , λ x → t

vis' : ∀ {E} {R}  -> ∀ {A : Type₀} -> E A -> (A -> itree E R) -> P₀ (itree-S E R) (itree E R)
vis' {A = A} e k = inr (A , e) , λ { (lift x) -> k x }

ret : ∀ {E} {R}  -> R -> itree E R
ret = in-fun ∘ ret'

tau : {E : Type₀ -> Type₁} -> {R : Type₀} -> itree E R -> itree E R
tau = in-fun ∘ tau'

vis : ∀ {E} {R}  -> ∀ {A : Type₀} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e = in-fun ∘ (vis' {A = A} e)
