{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order -- using (¬-<-zero; <-k+-cancel; _≤_)
open import Cubical.Categories.Category

open Precategory

private
  variable
    ℓ : Level


𝟛-hom : Fin 3 → Fin 3 → Type
𝟛-hom (x , _) (y , _) = x ≤ y

-- data 𝟛-ob {ℓ} : Type ℓ where
--   ① : 𝟛-ob
--   ② : 𝟛-ob
--   ③ : 𝟛-ob

-- data SingHom {X : Type ℓ} (x y : X) : Type (ℓ-suc ℓ) where
--   _⟶_ :

-- SingHom : ∀ {X : Type ℓ} (x y : X) → Type ℓ
-- SingHom {X = X} x y = Σ[ (a , b) ∈ X × X ] (a ≡ x) × (b ≡ y)

-- 𝟛-hom : Fin 3 → Fin 3 → Type
-- 𝟛-hom (0 , _) (0 , _) = SingHom 0 0
-- 𝟛-hom (1 , _) (1 , _) = SingHom 1 1
-- 𝟛-hom (2 , _) (2 , _) = SingHom 2 2
-- 𝟛-hom (0 , _) (1 , _) = SingHom 3 3
-- 𝟛-hom (0 , _) (2 , _) = SingHom 0 2
-- 𝟛-hom (1 , _) (2 , _) = SingHom 1 2
-- 𝟛-hom _ _ = ⊥


-- leqTrivP : ∀ {k m : ℕ} {e f : k ≤ m} → e ≡ f
-- leqTrivP {k} {m} {i , p} {j , q} = ΣPathP (left , toPathP right)
--   where
--     left : i ≡ j
--     left = inj-+m (p ∙ (sym q))

--     right : transp (λ i₁ → left i₁ + k ≡ m) i0 p ≡ q
--     right = isSetℕ (j + k) m (transp (λ i₁ → left i₁ + k ≡ m) i0 p) q

𝟛 : Precategory _ _
ob 𝟛 = Fin 3
Hom[_,_] 𝟛 = 𝟛-hom
id 𝟛 (x , _) = ≤-refl {x}
_⋆_ 𝟛 = ≤-trans
⋆IdL 𝟛 p = m≤n-isProp _ _
⋆IdR 𝟛 p = m≤n-isProp _ _
⋆Assoc 𝟛 f g h = m≤n-isProp _ _
