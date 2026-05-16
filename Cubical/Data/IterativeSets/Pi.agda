{-# OPTIONS --lossy-unification #-}

-- TODO: make type checking terminate
    
module Cubical.Data.IterativeSets.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Foundations.Transport

open import Cubical.Data.IterativeMultisets.Base renaming (index to index∞ ; elements to elements-V∞)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

private
  module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
    Inj : Type (ℓ-max ℓ ℓ')
    Inj = {x y : A} → f x ≡ f y → x ≡ y

apply⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → El⁰ x → V⁰ {ℓ}
apply⁰ {ℓ} {x} {y} Φ a = ⟨ elements x a , elements (y a) (Φ a) ⟩⁰

apply⁰-inj : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → Inj (apply⁰ {ℓ} {x} {y} Φ)
apply⁰-inj {ℓ} {x} {y} Φ {a} {b} p = isEmbedding→Inj {A = El⁰ x} {B = V⁰ {ℓ}} {f = elements x} (isEmbedding-elements x) a b (fst (orderedPair⁰≡orderedPair⁰ {x = elements x a} {y = elements (y a) (Φ a)} {a = elements x b} {b = elements (y b) (Φ b)} .fst p))

apply⁰-emb : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → isEmbedding (apply⁰ {ℓ} {x} {y} Φ)
apply⁰-emb {ℓ} {x} {y} Φ = injEmbedding {A = El⁰ x} {B = V⁰ {ℓ}} isSetV⁰ (apply⁰-inj {ℓ} {x} {y} Φ)

apply⁰-inj2' : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} (Φ Ψ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (a : El⁰ x) → apply⁰ {ℓ} {x} {y} Φ ≡ apply⁰ {ℓ} {x} {y} Ψ → Φ a ≡ Ψ a
apply⁰-inj2' {ℓ} {x} {y} Φ Ψ a p = {!!}

apply⁰-inj2 : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → Inj (apply⁰ {ℓ} {x} {y})
apply⁰-inj2 {ℓ} {x} {y} {Φ} {Ψ} p = funExt λ a → apply⁰-inj2' {ℓ} {x} {y} Φ Ψ a p

apply⁰-emb2 : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → isEmbedding (apply⁰ {ℓ} {x} {y})
apply⁰-emb2 {ℓ} {x} {y} = injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = El⁰ x → V⁰} {f = apply⁰ {ℓ} {x} {y}} (isSet→ {A' = V⁰ {ℓ}} {A = El⁰ {ℓ} x} (isSetV⁰ {ℓ})) (apply⁰-inj2 {ℓ} {x} {y})

graph⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
graph⁰ {ℓ} {x} {y} Φ = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = El⁰ x
    E .snd .fst = apply⁰ {ℓ} {x} {y} Φ
    E .snd .snd = apply⁰-emb {ℓ} {x} {y} Φ

graph⁰-helper : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (z : V⁰ {ℓ})
                  → ((z ∈⁰ graph⁰ Φ) ≡ fiber (apply⁰ {ℓ} {x} {y} Φ) z) -- (Σ[ a ∈ El⁰ x ] apply⁰ {ℓ} {x} {y} Φ a ≡ z))
graph⁰-helper {ℓ} {x} {y} Φ z = refl
-- propBiimpl→Equiv (isProp∈⁰ {x = graph⁰ Φ} {z = z}) (isEmbedding→hasPropFibers {f = apply⁰ {ℓ} {x} {y} Φ} (apply⁰-emb {ℓ} {x} {y} Φ) z) (idfun (z ∈⁰ graph⁰ Φ)) (idfun (fiber (apply⁰ Φ) z))
   
Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ {ℓ} x y = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = (a : El⁰ x) → El⁰ (y a)
    E .snd .fst = graph⁰
    E .snd .snd = {!!}

-- injEmbedding {A = (a : El⁰ x) → El⁰ (y a)} {B = V⁰ {ℓ}} isSetV⁰ λ {Φ Ψ : (a : El⁰ x) → El⁰ (y a)} (p : graph⁰ Φ ≡ graph⁰ Ψ) → (
--                   let
--                     P : ((z : V⁰ {ℓ}) → z ∈⁰ graph⁰ Φ → z ∈⁰ graph⁰ Ψ) × ((z : V⁰ {ℓ}) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ)
--                     P = ≡V⁰-≃-≃V⁰ {x = graph⁰ Φ} {y = graph⁰ Ψ} .fst p

--                     P₁ : (z : V⁰) → z ∈⁰ graph⁰ Φ → z ∈⁰ graph⁰ Ψ
--                     P₁ = P .fst

--                     s : (a : El⁰ x) → V⁰ {ℓ}
--                     s a = apply⁰ {ℓ} {x} {y} Φ a

--                     s∈Φ : (a : El⁰ x) → (s a) ∈⁰ (graph⁰ Φ)
--                     s∈Φ a = a , refl

--                     t : (a : El⁰ x) → index x
--                     t a = s∈Φ a .fst

--                     t-fib : (a : El⁰ x) → apply⁰ Φ a ≡ apply⁰ Φ a
--                     t-fib a = s∈Φ a .snd

--                     s∈Ψ : (a : El⁰ x) → (s a) ∈⁰ (graph⁰ Ψ)
--                     s∈Ψ a = P₁ (s a) (s∈Φ a)

--                     t' : (a : El⁰ x) → index x
--                     t' a = s∈Ψ a .fst

--                     t'-fib : (a : El⁰ x) → apply⁰ Ψ
--                                             (≡V⁰-≃-≃V⁰ .fst p .fst (apply⁰ Φ a)
--                                              (a , (λ _ → elements (graph⁰ Φ) a)) .fst)
--                                             ≡ apply⁰ Φ a
--                     t'-fib a = s∈Ψ a .snd

--                     goal' : (a : El⁰ x) → Φ a ≡ Ψ a
--                     goal' a = {!!}
                    
--                     goal : Φ ≡ Ψ
--                     goal = funExt goal'
--                   in goal)

-- private
--   module _ {ℓA ℓA' ℓB : Level} {A : Type ℓA} {A' : Type ℓA'} {B : A' → Type ℓB} (f : A → A') (g : (x : A) → B (f x)) where
--     Σfun : A → Σ A' B
--     Σfun x .fst = f x
--     Σfun x .snd = g x

--     InjFstInj : Inj f → Inj Σfun
--     InjFstInj injf p = injf (cong fst p)

-- private
--   module _ {ℓA ℓA' ℓB ℓB' : Level} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'} (setA' : isSet A') (f : A → A') (g : (x : A) → B x → B' (f x)) where
--       Σfun' : Σ A B → Σ A' B'
--       Σfun' pair .fst = f (pair .fst)
--       Σfun' pair .snd = uncurry g pair

--       InjΣInj : Inj f → ((x : A) → Inj (g x)) → Inj Σfun'
--       InjΣInj injf injg {a , b} {c , d} p = ΣPathTransport→PathΣ (a , b) (c , d) (q1 , q2)
--         where
--           s : Σ[ p1 ∈ f a ≡ f c ] subst B' p1 (g a b) ≡ g c d
--           s = PathΣ→ΣPathTransport _ _ p

--           q1 : a ≡ c
--           q1 = injf (s .fst)

--           p1' : f a ≡ f c
--           p1' = cong f q1

--           s1≡p1' : (s .fst) ≡ (cong f q1)
--           s1≡p1' = setA' (f a) (f c) (s .fst) (cong f q1)

--           p1'≡s1 : (cong f q1) ≡ s .fst
--           p1'≡s1 = setA' (f a) (f c) (cong f q1) (s .fst)

--           α : subst (λ z → B' (f z)) q1 (g a b) ≡ g c (subst B q1 b)
--           α = substCommSlice (λ z → B z) (λ z → B' (f z)) g (injf (s .fst)) b

--           β : subst (λ z → B' (f z)) q1 (g a b) ≡ subst B' (s .fst) (g a b)
--           β = cong (λ m → subst B' m (g a b)) p1'≡s1

--           p2 : g c (subst B q1 b) ≡ g c d
--           p2 = sym α ∙ β ∙ s .snd

--           q2 : subst B q1 b ≡ d
--           q2 = injg c p2

-- graph⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
-- graph⁰ {ℓ = ℓ} {x = x} {y = y} f = fromEmb E
--   where
--     E : Embedding (V⁰ {ℓ}) ℓ
--     E .fst = El⁰ x
--     E .snd .fst a = orderedPair⁰ (elements x a , elements (y a) (f a))
--     E .snd .snd = injEmbedding isSetV⁰ (λ {v} {w} p → isEmbedding→Inj {f = elements x} (isEmbedding-elements x) v w (orderedPair⁰≡orderedPair⁰ .fst p .fst))

-- Π⁰ : (x : V⁰ {ℓ}) → ((a : El⁰ x) → V⁰ {ℓ}) → V⁰ {ℓ}
-- Π⁰ {ℓ} x y = fromEmb E
--   where
--     In : {f g : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)} → graph⁰ {x = x} {y = y} f ≡ graph⁰ {x = x} {y = y} g → (a : El⁰ x) → f a ≡ g a
--     In {f} {g} p a = 
--       let
--         ∈⁰graph⁰-f→g : ((z : V⁰) → z ∈⁰ graph⁰ f → z ∈⁰ graph⁰ g)
--         ∈⁰graph⁰-f→g = ≡V⁰-≃-≃V⁰ .fst p .fst

--         p : Σ[ a' ∈ El⁰ x ] orderedPair⁰ ((elements x a') , (elements (y a') (g a'))) ≡ orderedPair⁰ ((elements x a) , (elements (y a) (f a)))
--         p = ∈⁰graph⁰-f→g (orderedPair⁰ ((elements x a) , (elements (y a) (f a)))) (a , refl)

--         a' : El⁰ x
--         a' = p .fst

--         p₂ : orderedPair⁰ ((elements x a') , (elements (y a') (g a'))) ≡ orderedPair⁰ ((elements x a) , (elements (y a) (f a)))
--         p₂ = p .snd

--         q : elements x a' ≡ elements x a
--         q = orderedPair⁰≡orderedPair⁰ .fst p₂ .fst

--         r : a' ≡ a
--         r = isEmbedding→Inj {f = elements x} (isEmbedding-elements x) a' a q

--         s : elements (y a') (g a') ≡ elements (y a) (f a)
--         s = orderedPair⁰≡orderedPair⁰ .fst p₂ .snd
        
--         t : elements (y a) (g a) ≡ elements (y a') (g a')
--         t i = elements (y (r (~ i))) (g (r (~ i)))

--         goal : f a ≡ g a
--         goal = isEmbedding→Inj {f = elements (y a)} (isEmbedding-elements (y a)) (f a) (g a) (sym (t ∙ s))
--       in goal
       
    
--     In' : {f g : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)} → graph⁰ {x = x} {y = y} f ≡ graph⁰ {x = x} {y = y} g → f ≡ g
--     In' p = funExt (In p)

--     E : Embedding (V⁰ {ℓ}) ℓ
--     E .fst = (a : El⁰ x) → El⁰ (y a)
--     E .snd .fst f = graph⁰ {x = x} {y = y} f
--     E .snd .snd = injEmbedding isSetV⁰ In'

-- El⁰Π⁰isΠ : El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
-- El⁰Π⁰isΠ = refl

-- _→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
-- x →⁰ y = Π⁰ x (λ _ → y)

-- El⁰→⁰is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
-- El⁰→⁰is→ = refl
