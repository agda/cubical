{-

This file contains:

- Definitions of fibers and equivalences

- Glue types

- The identity equivalence and the ua constant

- Proof of univalence using that unglue is an equivalence ([EquivContr])


It should *not* depend on the Agda standard library

-}
{-# OPTIONS --cubical #-}
module Cubical.Core.Glue where

open import Cubical.Core.Prelude

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

-- Make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ-max ℓ ℓ') where
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv public

infix 4 _≃_

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e

equivIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd

-- TODO: Maybe change the internal definition of equivalence to "any
-- partial element can be extended to a total one"?
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN  equivFun #-}

-- I don't know why this should be a module...
module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

open GluePrims public
  renaming ( primGlue to Glue
           ; prim^glue to glue
           ; prim^unglue to unglue)

-- The identity equivalence
idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , λ { .equiv-proof y → (y , refl) , \ z → contrSingl (z .snd) }

-- The ua constant
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  Glue B
       -- Why is this argument needed? Apparently Agda doesn't infer
       -- things where it has to do pattern-matching...
       (λ {(i = i0) → _ ; (i = i1) → _})
       (λ {(i = i0) → e ; (i = i1) → idEquiv B})


-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (T : Partial φ (Set ℓ))
  (f : PartialP φ λ o → (T o) ≃ A) → isEquiv {A = Glue A T f} (unglue {φ = φ})
equiv-proof (unglueIsEquiv A φ T f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1) b .snd i }
      ctr : fiber (unglue {φ = φ}) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1) b .fst }) (hcomp u b)
            , λ j → hfill u (inc b) j)
  in ( ctr
     , λ (v : fiber (unglue {φ = φ}) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1) b v i .snd j
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .snd  j }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1) b v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inc b) j))

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I)
                (T : Partial φ (Set ℓ))
                (f : PartialP φ (λ o → (T o) ≃ A)) →
                (Glue A T f) ≃ A
unglueEquiv A φ T f = unglue {φ = φ} , unglueIsEquiv A φ T f

-- The univalence theorem
EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr A = ( A , idEquiv A)
               , λ w i → let T : Partial (~ i ∨ i) (Set _)
                             T = λ { (i = i0) → A ; (i = i1) → w .fst }
                             f : PartialP (~ i ∨ i) (λ x → T x ≃ A)
                             f = λ { (i = i0) → idEquiv A ; (i = i1) → w .snd }
                         in ( Glue A T f , unglueEquiv _ _ T f)
