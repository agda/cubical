{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.EilenbergSteenrod where

{-
This module contains the Eilenberg-Steenrod axioms for ordinary reduced cohomology theories with binary additivity.
The axioms are based on the ones given in Cavallo's MSc thesis (https://www.cs.cmu.edu/~ecavallo/works/thesis15.pdf) and Buchholtz/Favonia (2018)
-}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Int

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open GroupEquiv
open GroupHom

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

cofib : (f : A → B) → Type _
cofib f = Pushout (λ _ → tt) f

cfcod : (f : A → B) → B → cofib f
cfcod f = inr

suspFun : (f : A → B) → Susp A → Susp B
suspFun f north = north
suspFun f south = south
suspFun f (merid a i) = merid (f a) i

contravar :  (H : Pointed ℓ → AbGroup {ℓ'}) → Type _
contravar {ℓ = ℓ} H = {A B : Pointed ℓ} (f : A →∙ B) → AbGroupHom (H B) (H A)

record isCohomTheory {ℓ : Level} (H : (n : Int) → Pointed ℓ → AbGroup {ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  where
  field
    f* : (n : Int) → contravar (H n)
    Suspension : Σ[ F ∈ ((n : Int) {A : Pointed ℓ} → AbGroupEquiv (H (sucInt n) (Susp (typ A) , north)) (H n A)) ]
                   ({A B : Pointed ℓ} (f : A →∙ B) (n : Int)
               → fun (f* (sucInt n) (suspFun (fst f) , refl)) ∘ invEq (eq (F n {A = B}))
                ≡ invEq (eq (F n {A = A})) ∘ fun (f* n f))
    Exactness : {A B : Pointed ℓ}  (f : A →∙ B) → (n :  Int)
              → ((x : _) → isInKer _ _ (f* n {A = A} {B = B} f) x
                          → isInIm _ _ (f* n {A = B} {B = _ , inr (pt B)} (cfcod (fst f) , refl)) x)
               × ((x : _) → isInIm _ _ (f* n {A = B} {B = _ , inr (pt B)} (cfcod (fst f) , refl)) x
                          → isInKer _ _ (f* n {A = A} {B = B} f) x)
    Dimension : (n : ℕ) → isContr (fst (H (pos (suc n)) (Lift (Bool) , lift true)))
                          × isContr (fst (H (negsuc n) (Lift (Bool) , lift true)))
    BinaryWedge : (n : Int) {A B : Pointed ℓ} → AbGroupEquiv (H n (A ⋁ B , (inl (pt A)))) (dirProdAb (H n A) (H n B))
