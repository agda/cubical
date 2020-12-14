{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.EilenbergSteenrod where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.HITs.SetTruncation renaming (map to sMap)
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec ; map to trMap)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

open import Cubical.HITs.Pushout
open import Cubical.Algebra.Group
open import Cubical.HITs.Susp

open IsGroup
open GroupStr
open GroupIso
open import Cubical.Data.Bool

open import Cubical.HITs.Wedge

open GroupHom
cofib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type _
cofib f = Pushout (λ _ → tt) f

cfcod : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → B → cofib f
cfcod f = inr 

suspFun : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Susp A → Susp B
suspFun f north = north
suspFun f south = south
suspFun f (merid a i) = merid (f a) i

contravar : ∀ {ℓ''} (H : Type ℓ-zero → Group {ℓ''}) → Type _
contravar H = {A : Type ℓ-zero} {B : Type ℓ-zero} → (f : A → B) → GroupHom (H B) (H A)

open import Cubical.Data.Sigma

record isCohomTheory (H : (n : ℕ) → Type ℓ-zero → Group {ℓ-zero}) (f* : (n : ℕ) → contravar {ℓ-zero} (H n))  : Type₁ where
  _* : {A B : Type ℓ-zero} (f : B → A) (n : ℕ) → fst (H n A) → fst (H n B)
  _* f n = GroupHom.fun (f* n f)
  
  field
    Suspension : Σ[ F ∈ ((n : ℕ) {A : Pointed ℓ-zero} → GroupIso (H (suc n) (Susp (typ A))) (H n (typ A))) ]
                   ({A B : Pointed ℓ-zero} (f : typ A → typ B) (n : ℕ)
               → fun (f* (suc n) (suspFun f)) ∘ inv (F n {A = B})
                ≡ inv (F n {A = A}) ∘ fun (f* n f))
    Exactness : {A B : Pointed ℓ-zero}  (f : A →∙ B) → (n :  ℕ)
              → ((x : _) → (isInKer _ _ (f* n (fst f)) x) → isInIm _ _ (f* n (cfcod (fst f))) x)
               × ((x : _) → isInIm _ _ (f* n (cfcod (fst f))) x → isInKer _ _ (f* n (fst f)) x)
    Dimension : (n : ℕ) → isContr (fst (H (suc n) Bool))
    BinaryWedge : (n : ℕ) {A B : Pointed ℓ-zero} → GroupIso (H (suc n) (A ⋁ B)) (dirProd (H (suc n) (typ A)) (H (suc n) (typ B)))
