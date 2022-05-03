{-# OPTIONS --safe #-}

module Cubical.Homotopy.EilenbergSteenrod where

{-
This module contains the Eilenberg-Steenrod axioms for ordinary
reduced cohomology theories with binary additivity.
The axioms are based on the ones given in Cavallo's MSc thesis
(https://www.cs.cmu.edu/~ecavallo/works/thesis15.pdf) and
Buchholtz/Favonia (2018)
-}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Int

open import Cubical.Algebra.Group hiding (ℤ ; Bool)
open import Cubical.Algebra.AbGroup

record coHomTheory {ℓ ℓ' : Level} (H : (n : ℤ) → Pointed ℓ → AbGroup ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  where
  Boolℓ : Pointed ℓ
  Boolℓ = Lift Bool , lift true
  field
    Hmap : (n : ℤ) → {A B : Pointed ℓ} (f : A →∙ B) → AbGroupHom (H n B) (H n A)
    Suspension : Σ[ F ∈ ((n : ℤ) {A : Pointed ℓ} → AbGroupEquiv (H (sucℤ n) (Susp (typ A) , north)) (H n A)) ]
                   ({A B : Pointed ℓ} (f : A →∙ B) (n : ℤ)
               → fst (Hmap (sucℤ n) (suspFun (fst f) , refl)) ∘ invEq (fst (F n {A = B}))
                ≡ invEq (fst (F n {A = A})) ∘ fst (Hmap n f))
    Exactness : {A B : Pointed ℓ}  (f : A →∙ B) (n :  ℤ)
              → Ker (Hmap n f)
               ≡ Im (Hmap n {B = _ , inr (pt B)} (cfcod (fst f) , refl))
    Dimension : (n : ℤ) → ¬ n ≡ 0 → isContr (fst (H n Boolℓ))
    BinaryWedge : (n : ℤ) {A B : Pointed ℓ} → AbGroupEquiv (H n (A ⋁ B , (inl (pt A)))) (dirProdAb (H n A) (H n B))
