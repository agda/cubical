{-

Definition of a homogeneous pointed type, and proofs that pi, product, path, and discrete types are homogeneous

Portions of this file adapted from Nicolai Kraus' code here:
  https://bitbucket.org/nicolaikraus/agda/src/e30d70c72c6af8e62b72eefabcc57623dd921f04/trunc-inverse.lagda

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Homogeneous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Structures.Pointed

isHomogeneous : ∀ {ℓ} → Pointed ℓ → Type (ℓ-suc ℓ)
isHomogeneous {ℓ} (A , x) = ∀ y → Path (Pointed ℓ) (A , x) (A , y)


isHomogeneousPi : ∀ {ℓ ℓ'} {A : Type ℓ} {B∙ : A → Pointed ℓ'}
                 → (∀ a → isHomogeneous (B∙ a)) → isHomogeneous (Πᵘ∙ A B∙)
isHomogeneousPi h f i .fst = ∀ a → typ (h a (f a) i)
isHomogeneousPi h f i .snd a = pt (h a (f a) i)

isHomogeneousProd : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'}
                   → isHomogeneous A∙ → isHomogeneous B∙ → isHomogeneous (A∙ ×∙ B∙)
isHomogeneousProd hA hB (a , b) i .fst = typ (hA a i) × typ (hB b i)
isHomogeneousProd hA hB (a , b) i .snd .fst = pt (hA a i)
isHomogeneousProd hA hB (a , b) i .snd .snd = pt (hB b i)

isHomogeneousPath : ∀ {ℓ} (A : Type ℓ) {x y : A} (p : x ≡ y) → isHomogeneous ((x ≡ y) , p)
isHomogeneousPath A {x} {y} p q
  = pointed-sip ((x ≡ y) , p) ((x ≡ y) , q) (eqv , compPathr-cancel p q)
  where eqv : (x ≡ y) ≃ (x ≡ y)
        eqv = compPathlEquiv (q ∙ sym p)

module HomogeneousDiscrete {ℓ} {A∙ : Pointed ℓ} (dA : Discrete (typ A∙)) (y : typ A∙) where

  -- switches pt A∙ with y
  switch : typ A∙ → typ A∙
  switch x with dA x (pt A∙)
  ...         | yes _ = y
  ...         | no _ with dA x y
  ...                | yes _  = pt A∙
  ...                | no  _  = x

  switch-ptA∙ : switch (pt A∙) ≡ y
  switch-ptA∙ with dA (pt A∙) (pt A∙)
  ...         | yes _ = refl
  ...         | no ¬p = ⊥.rec (¬p refl)

  switch-idp : ∀ x → switch (switch x) ≡ x
  switch-idp x with dA x (pt A∙)
  switch-idp x | yes p with dA y (pt A∙)
  switch-idp x | yes p | yes q = q ∙ sym p
  switch-idp x | yes p | no  _ with dA y y
  switch-idp x | yes p | no  _ | yes _ = sym p
  switch-idp x | yes p | no  _ | no ¬p = ⊥.rec (¬p refl)
  switch-idp x | no ¬p with dA x y
  switch-idp x | no ¬p | yes p with dA y (pt A∙)
  switch-idp x | no ¬p | yes p | yes q = ⊥.rec (¬p (p ∙ q))
  switch-idp x | no ¬p | yes p | no  _ with dA (pt A∙) (pt A∙)
  switch-idp x | no ¬p | yes p | no  _ | yes _ = sym p
  switch-idp x | no ¬p | yes p | no  _ | no ¬q = ⊥.rec (¬q refl)
  switch-idp x | no ¬p | no ¬q with dA x (pt A∙)
  switch-idp x | no ¬p | no ¬q | yes p = ⊥.rec (¬p p)
  switch-idp x | no ¬p | no ¬q | no  _ with dA x y
  switch-idp x | no ¬p | no ¬q | no  _ | yes q = ⊥.rec (¬q q)
  switch-idp x | no ¬p | no ¬q | no  _ | no  _ = refl

  switch-eqv : typ A∙ ≃ typ A∙
  switch-eqv = isoToEquiv (iso switch switch switch-idp switch-idp)

isHomogeneousDiscrete : ∀ {ℓ} {A∙ : Pointed ℓ} (dA : Discrete (typ A∙)) → isHomogeneous A∙
isHomogeneousDiscrete {ℓ} {A∙} dA y
  = pointed-sip (typ A∙ , pt A∙) (typ A∙ , y) (switch-eqv , switch-ptA∙)
  where open HomogeneousDiscrete {ℓ} {A∙} dA y
