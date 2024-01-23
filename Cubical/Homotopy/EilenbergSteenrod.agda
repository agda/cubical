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

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Pi

open import Cubical.Axiom.Choice

record coHomTheory {ℓ ℓ' : Level} (H : (n : ℤ) → Pointed ℓ → AbGroup ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  where
  Boolℓ : Pointed ℓ
  Boolℓ = Lift Bool , lift true
  field
    Hmap : (n : ℤ) → {A B : Pointed ℓ} (f : A →∙ B) → AbGroupHom (H n B) (H n A)
    HMapComp : (n : ℤ) → {A B C : Pointed ℓ} (g : B →∙ C) (f : A →∙ B)
      → compGroupHom (Hmap n g) (Hmap n f) ≡ Hmap n (g ∘∙ f)
    HMapId : (n : ℤ) → {A : Pointed ℓ} → Hmap n (idfun∙ A) ≡ idGroupHom
    Suspension : Σ[ F ∈ ((n : ℤ) {A : Pointed ℓ} → AbGroupEquiv (H (sucℤ n) (Susp (typ A) , north)) (H n A)) ]
                   ({A B : Pointed ℓ} (f : A →∙ B) (n : ℤ)
               → fst (Hmap (sucℤ n) (suspFun (fst f) , refl)) ∘ invEq (fst (F n {A = B}))
                ≡ invEq (fst (F n {A = A})) ∘ fst (Hmap n f))
    Exactness : {A B : Pointed ℓ}  (f : A →∙ B) (n :  ℤ)
              → Ker (Hmap n f)
               ≡ Im (Hmap n {B = _ , inr (pt B)} (cfcod (fst f) , refl))
    Dimension : (n : ℤ) → ¬ n ≡ 0 → isContr (fst (H n Boolℓ))
    BinaryWedge : (n : ℤ) {A B : Pointed ℓ} → AbGroupEquiv (H n (A ⋁ B , (inl (pt A)))) (dirProdAb (H n A) (H n B))

record coHomTheoryGen {ℓ ℓ' : Level} (H : (n : ℤ) → Pointed ℓ → AbGroup ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  where
  Boolℓ : Pointed ℓ
  Boolℓ = Lift Bool , lift true
  field
    Hmap : (n : ℤ) → {A B : Pointed ℓ} (f : A →∙ B) → AbGroupHom (H n B) (H n A)
    HMapComp : (n : ℤ) → {A B C : Pointed ℓ} (g : B →∙ C) (f : A →∙ B)
      → compGroupHom (Hmap n g) (Hmap n f) ≡ Hmap n (g ∘∙ f)
    HMapId : (n : ℤ) → {A : Pointed ℓ} → Hmap n (idfun∙ A) ≡ idGroupHom

    Suspension : Σ[ F ∈ ((n : ℤ) {A : Pointed ℓ} → AbGroupEquiv (H (sucℤ n) (Susp (typ A) , north)) (H n A)) ]
                   ({A B : Pointed ℓ} (f : A →∙ B) (n : ℤ)
               → fst (Hmap (sucℤ n) (suspFun (fst f) , refl)) ∘ invEq (fst (F n {A = B}))
                ≡ invEq (fst (F n {A = A})) ∘ fst (Hmap n f))
    Exactness : {A B : Pointed ℓ}  (f : A →∙ B) (n :  ℤ)
              → Ker (Hmap n f)
               ≡ Im (Hmap n {B = _ , inr (pt B)} (cfcod (fst f) , refl))
    Dimension : (n : ℤ) → ¬ n ≡ 0 → isContr (fst (H n Boolℓ))
    Wedge : (n : ℤ) {I : Type ℓ} (satAC : satAC (ℓ-max ℓ ℓ') 2 I) {A : I → Pointed ℓ}
      → isEquiv {A = H n (⋁gen∙ I A) .fst}
                 {B = ΠAbGroup (λ i → H n (A i)) .fst}
                 λ x i → Hmap n ((λ x → inr (i , x)) , sym (push i)) .fst x

  Wedge→AbGroupEquiv : (n : ℤ) {I : Type ℓ} (satAC : satAC (ℓ-max ℓ ℓ') 2 I) {A : I → Pointed ℓ}
    → AbGroupEquiv (H n (⋁gen∙ I A)) (ΠAbGroup (λ i → H n (A i)) )
  fst (fst (Wedge→AbGroupEquiv n satAC)) = _
  snd (fst (Wedge→AbGroupEquiv n satAC)) = Wedge n satAC
  snd (Wedge→AbGroupEquiv n satAC) = makeIsGroupHom λ f g
    → funExt λ i → IsGroupHom.pres· (Hmap n ((λ x → inr (i , x)) , sym (push i)) .snd) _ _
