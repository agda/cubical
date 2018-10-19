{-

This file contains:

- Definitions of fibers, isContr and equivalences

- Glue types

- The identity equivalence and the ua constant


It should *not* depend on the Agda standard library

 -}
{-# OPTIONS --cubical #-}
module Cubical.Glue where

open import Cubical.Prelude

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

isContr : {ℓ : Level} (A : Set ℓ) → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  contrFibers : (A → B) → Set (ℓ-max ℓ ℓ')
  contrFibers f = (y : B) → isContr (fiber f y)

  record isEquiv (f : A → B) : Set (ℓ-max ℓ ℓ') where
    field
      equiv-proof : contrFibers f

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

open isEquiv public

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e

-- TODO: Maybe change the internal definition of equivalence?
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN  equivFun #-}

-- I don't know why this should be a module...
module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial (Set ℓ') φ) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

open GluePrims public
  renaming ( primGlue to Glue
           ; prim^glue to glue
           ; prim^unglue to unglue)

-- The identity equivalence
idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , (λ { .equiv-proof y → (y , refl) , \ z → contrSingl (z .snd)  })

-- The ua constant
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  Glue B
       -- Why is this argument needed? Apparently Agda doesn't infer
       -- things where it has to do pattern-matching...
       (λ {(i = i0) → _ ; (i = i1) → _})
       (λ {(i = i0) → e ; (i = i1) → idEquiv B})

-- Proof of univalence using that unglue is an equivalence:

unglueIsEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (T : Partial (Set ℓ) φ)
  (f : PartialP φ λ o → (T o) ≃ A) → isEquiv (Glue A T f) A (unglue {φ = φ})
unglueIsEquiv A φ T f = λ { .equiv-proof b → rem b }
  where
  rem : (b : A) → isContr (fiber (unglue {φ = φ}) b)
  rem b =
    let u : I → Partial A φ
        u i = λ{ (φ = i1) → f 1=1 .snd .equiv-proof b .fst .snd i }
        ctr : fiber (unglue {φ = φ}) b
        ctr = ( glue (λ{ (φ = i1) → f 1=1 .snd .equiv-proof b .fst .fst }) (hcomp u b)
              , λ j → hfill u (inc b) j)
    in ( ctr
       , λ v i →
         let u' : I → Partial A (φ ∨ ~ i ∨ i)
             u' j = λ { (φ = i1) → f 1=1 .snd .equiv-proof b .snd v i .snd j
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .snd  j }
         in ( glue (λ{ (φ = i1) → f 1=1 .snd .equiv-proof b .snd v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inc b) j))

unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (T : Partial (Set ℓ) φ)
                (f : PartialP φ (λ o → (T o) ≃ A)) →
                (Glue A T f) ≃ A
unglueEquiv A φ T f = unglue {φ = φ} , unglueIsEquiv A φ T f

EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr A = (A , idEquiv A) , (λ w i →
  let φ = ~ i ∨ i
      Tf : Partial (Σ[ T ∈ _ ] T ≃ A) φ
      Tf = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
   in ( Glue A {φ = φ} (λ o → fst (Tf o)) (λ o → snd (Tf o))
      , unglueEquiv A φ (λ o → fst (Tf o)) (λ o → snd (Tf o))))
