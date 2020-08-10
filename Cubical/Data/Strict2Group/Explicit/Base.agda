
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Explicit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Data.Strict2Group.Explicit.Notation

record Strict2GroupExp ℓ : Type (ℓ-suc ℓ) where
  constructor strict2groupexp
  field
    -- a group of objects and a group of morphisms
    C₀ : Group ℓ
    C₁ : Group ℓ

    -- source and target morphisms
    s : morph C₁ C₀
    t : morph C₁ C₀

    -- identity morphism
    i : morph C₀ C₁
    -- the composition map C₁×₀C₁→C₁
    ∘ : (g f : Group.type C₁) → (s .fst) g ≡ (t .fst f) → Group.type C₁

  open S2GBaseNotation C₀ C₁ s t i ∘

  field
    si : (x : TC₀) → src (id x) ≡ x
    ti : (x : TC₀) → tar (id x) ≡ x

    s∘ : (g f : TC₁) → (c : CohCond g f) → src (∘ g f c) ≡ src f
    t∘ : (g f : TC₁) → (c : CohCond g f) → tar (∘ g f c) ≡ tar g

    -- composition operation defines a homomorphism that is associative and unital w.r.t. i
    isMorph∘ : ∀ {g f g' f' : TC₁} (c : CohCond g f) (c' : CohCond g' f')
      → ∘ (g ∙₁ g') (f ∙₁ f') (∙c c c') ≡ (∘ g f c) ∙₁ (∘ g' f' c')

    assoc∘ : ∀ {h g f : TC₁} → (c1 : CohCond g f) → (c2 : CohCond h g)
      → ∘ (∘ h g c2) f ((s∘ h g c2) ∙ c1) ≡  ∘ h (∘ g f c1) (c2 ∙ (sym (t∘ g f c1)))

    lUnit∘ : (f : TC₁) → ∘ (id (tar f)) f (si (tar f)) ≡ f
    rUnit∘ : (f : TC₁) → ∘ f (id (src f)) (sym (ti (src f))) ≡ f
