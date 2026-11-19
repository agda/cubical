{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.ConnectedCovers.EquivPreservation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv ; pathToEquivRefl)

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Nat renaming (elim to natElim)
open import Cubical.HITs.Susp
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadsLemma

open import Cubical.Homotopy.Serre.HomotopyGroups

open import Cubical.Homotopy.Serre.ConnectedCovers.GeneralisingFreudenthal
open import Cubical.Homotopy.Serre.ConnectedCovers.PointedEquivalences

open import Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base
open import Cubical.Homotopy.Serre.FiberOrCofiberSequences.LongExactSequence


private
  variable
    ℓ : Level
idEquivInv : {X : Type ℓ} → fst (invEquiv (idEquiv X)) ≡ fst (idEquiv X)
idEquivInv = refl

GroupIsoEquiv : (G H : Group ℓ) → GroupIso G H → GroupEquiv G H
GroupIsoEquiv G H (h , hHom) = (isoToEquiv h) , hHom

invPathToEquivRefl : {X : Type ℓ}
                   → fst (invEquiv (pathToEquiv (refl {x = X})))
                   ≡ fst (idEquiv X)
invPathToEquivRefl {X = X} = (λ i → (fst (invEquiv (pathToEquivRefl i))))
                           ∙ idEquivInv

→∙pathToEquivPreserves : {X Y Z : Pointed ℓ} (n : ℕ)
                       → (e : Y ≡ Z)
                       → (f : X →∙ Z)
                       → isEquiv (fst f)
                       → isEquiv
                          (fst
                           ((fst (invEquiv
                            (pathToEquiv (λ i → (X →∙ (e i)))))) f))
→∙pathToEquivPreserves {X = X} n =
  J (λ Z e → (f : X →∙ Z)
          → isEquiv (fst f)
          → isEquiv (fst
                     ((fst (invEquiv
                      (pathToEquiv (λ i → (X →∙ (e i)))))) f)))
    λ f hf →
    transport (λ i → isEquiv (fst (invPathToEquivRefl (~ i) f))) hf

→∙pathToEquivPreserves' : {X Y Z : Pointed ℓ} (n : ℕ)
                        → (e : X ≡ Y)
                        → (f : Y →∙ Z)
                        → isEquiv (πFun n f)
                        → isEquiv (πFun n
                                   (fst (invEquiv
                                   (pathToEquiv (λ i → ((e i) →∙ Z)))) f))
→∙pathToEquivPreserves' {Z = Z} n =
  J (λ Y e → (f : Y →∙ Z)
           → isEquiv (πFun n f)
           → isEquiv (πFun n
                      (fst (invEquiv
                      (pathToEquiv (λ i → ((e i) →∙ Z)))) f)))
    λ f hf → transport (λ i → isEquiv (πFun n (invPathToEquivRefl (~ i) f)))
                        hf

GroupHom-pathToEquivPreserves : {X Y Z : Group ℓ}
                             → (e : Y ≡ Z)
                             → (f : GroupHom X Z)
                             → isEquiv (fst f)
                             → isEquiv
                                (fst (fst (invEquiv
                                (pathToEquiv (λ i → (GroupHom X (e i))))) f))
GroupHom-pathToEquivPreserves {X = X} =
  J (λ Z e → (f : GroupHom X Z) → isEquiv (fst f)
           → isEquiv (fst (fst (invEquiv
                      (pathToEquiv (λ i → (GroupHom X (e i))))) f)))
    λ f hf →
    transport (λ i → isEquiv (fst (invPathToEquivRefl (~ i) f))) hf

GroupHom-pathToEquivPreserves' : {X Y Z : Group ℓ}
                              → (e : X ≡ Y)
                              → (f : GroupHom Y Z)
                              → isEquiv (fst f)
                              → isEquiv (fst (fst (invEquiv
                                 (pathToEquiv (λ i → (GroupHom (e i) Z)))) f))
GroupHom-pathToEquivPreserves' {Z = Z} =
  J (λ Y e → (f : GroupHom Y Z) → isEquiv (fst f)
           → isEquiv (fst (fst (invEquiv
                      (pathToEquiv (λ i → (GroupHom (e i) Z)))) f)))
    λ f hf →
    transport (λ i → isEquiv (fst (invPathToEquivRefl (~ i) f))) hf


AbGroupHom-pathToEquivPreserves : {X Y Z : AbGroup ℓ}
                               → (e : Y ≡ Z)
                               → (f : AbGroupHom X Z)
                               → isEquiv (fst f)
                               → isEquiv
                                  (fst (fst (invEquiv
                                  (pathToEquiv
                                  (λ i → (AbGroupHom X (e i))))) f))
AbGroupHom-pathToEquivPreserves {X = X} =
  J (λ Z e → (f : AbGroupHom X Z) → isEquiv (fst f)
           → isEquiv (fst (fst (invEquiv
                      (pathToEquiv (λ i → (AbGroupHom X (e i))))) f)))
    λ f hf
    → transport (λ i → isEquiv (fst (invPathToEquivRefl (~ i) f))) hf


LoopAbHomZeroAux : (X : Pointed ℓ) → πGr 0 (Ω X) ≡ (AbGroup→Group (πAb 0 X))
LoopAbHomZeroAux X = uaGroup (GroupIsoEquiv (πGr 0 (Ω X)) (πGr 1 X) (GrIso-πΩ-π 0))

LoopAbHomZero : (G : AbGroup ℓ) (X : Pointed ℓ)
  → GroupHom (AbGroup→Group G) (πGr 0 (Ω X)) ≃ AbGroupHom G (πAb 0 X)
LoopAbHomZero G X =
  pathToEquiv
  λ i →
    GroupHom
     (AbGroup→Group G)
     (LoopAbHomZeroAux X i)

LoopAbHomZeroPreservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ)
  → (f : AbGroupHom G (πAb 0 X))
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (LoopAbHomZero G X)) f))
LoopAbHomZeroPreservesEquiv G X =
  GroupHom-pathToEquivPreserves (LoopAbHomZeroAux X)

LoopAbHomNAux : (X : Pointed ℓ) (n : ℕ) → (AbGroup→Group (πAb n (Ω X))) ≡ (AbGroup→Group (πAb (1 + n) X))
LoopAbHomNAux X n = uaGroup (GroupIsoEquiv (πGr (1 + n) (Ω X)) (πGr (2 + n) X) (GrIso-πΩ-π (1 + n)))

LoopAbHomN : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → AbGroupHom G (πAb n (Ω X)) ≃ AbGroupHom G (πAb (1 + n) X)
LoopAbHomN G X n = pathToEquiv
                   (λ i →
                        GroupHom (AbGroup→Group G)
                                 (LoopAbHomNAux X n i))

LoopAbHomNPreservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (f : AbGroupHom G (πAb (1 + n) X))
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (LoopAbHomN G X n)) f))
LoopAbHomNPreservesEquiv G X n =
  GroupHom-pathToEquivPreserves (LoopAbHomNAux X n)

→∙CommEquivΩ^ : (X Y : Pointed ℓ) (n : ℕ)
  → (Y →∙ ((Ω^ (1 + n)) X)) ≃ (Y →∙ ((Ω^ n) (Ω X)))
→∙CommEquivΩ^ X Y n = pathToEquiv (λ i → (Y →∙ (flipΩPath {A = X} n i)))

→∙CommEquivΩ^-preservesEquiv : (X Y : Pointed ℓ) (n : ℕ)
  → (f : Y →∙ ((Ω^ n) (Ω X)))
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (→∙CommEquivΩ^ X Y n)) f))
→∙CommEquivΩ^-preservesEquiv X Y n =
  →∙pathToEquivPreserves n (flipΩPath {A = X} n)

GroupHomEq : (G H : Group ℓ) → GroupEquiv G H → (K : Group ℓ)
  → (GroupHom G K) ≃ (GroupHom H K)
GroupHomEq G H hyp K =
  pathToEquiv (λ i → GroupHom ((fst (GroupPath G H)) hyp i) K)

GroupHomEqPreservesEquiv : (G H : Group ℓ) (e : GroupEquiv G H) (K : Group ℓ)
  → (f : GroupHom H K)
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (GroupHomEq G H e K)) f))
GroupHomEqPreservesEquiv G H e K =
  GroupHom-pathToEquivPreserves' (fst (GroupPath G H) e)

GroupHomEq' : (G H : Group ℓ) → GroupEquiv G H → (K : Group ℓ)
  → (GroupHom K H) ≃ (GroupHom K G)
GroupHomEq' G H hyp K =
  pathToEquiv (λ i → GroupHom K ((fst (GroupPath G H)) hyp (~ i)))

GroupHomEq'PreservesEquiv : (G H : Group ℓ) (e : GroupEquiv G H) (K : Group ℓ)
  → (f : GroupHom K G)
  → isEquiv (fst f)
  → isEquiv (fst (fst (invEquiv (GroupHomEq' G H e K)) f))
GroupHomEq'PreservesEquiv G H e K =
  GroupHom-pathToEquivPreserves ((fst (GroupPath G H) e) ⁻¹)

→∙CommEquivSusp^ : (X Y : Pointed ℓ) (n : ℕ)
  → (^Susp∙ (1 + n) X →∙ Y) ≃ (Susp∙^ (1 + n) X →∙ Y)
→∙CommEquivSusp^ X Y n =
  pathToEquiv (λ i → ((Susp∙^Comm' X (1 + n) (~ i)) →∙ Y))

→∙CommEquivSusp^-preservesEquiv : (X Y : Pointed ℓ) (m n : ℕ)
  → (f : Susp∙^ (1 + n) X →∙ Y)
  → isEquiv (πFun m f)
  → isEquiv (πFun m
             (fst (invEquiv (→∙CommEquivSusp^ X Y n)) f))
→∙CommEquivSusp^-preservesEquiv X Y m n =
  →∙pathToEquivPreserves' m ((Susp∙^Comm' X (1 + n)) ⁻¹)

EM-raw∙≡CommSuspEM1 : (G : AbGroup ℓ) (n : ℕ)
  → EM-raw∙ G (2 + n) ≡ ^Susp∙ (1 + n) (EM∙ G 1)
EM-raw∙≡CommSuspEM1 G zero = refl
EM-raw∙≡CommSuspEM1 G (suc n) = cong (Susp∙ ∘ typ) (EM-raw∙≡CommSuspEM1 G n)

EM-raw∙-SuspEM1Eq : (G : AbGroup ℓ) (X : Pointed ℓ) (n : ℕ)
  → (EM-raw∙ G (2 + n) →∙ X) ≃ (^Susp∙ (1 + n) (EM∙ G 1) →∙ X)
EM-raw∙-SuspEM1Eq G X n =
  pathToEquiv (λ i → ((EM-raw∙≡CommSuspEM1 G n i) →∙ X))

EM-raw∙-SuspEM1Eq-preservesEquiv : (G : AbGroup ℓ) (X : Pointed ℓ) (m n : ℕ)
  → (f : ^Susp∙ (1 + n) (EM∙ G 1) →∙ X)
  → isEquiv (πFun m f)
  → isEquiv
     (πFun m
     (fst (invEquiv
     (EM-raw∙-SuspEM1Eq G X n)) f))
EM-raw∙-SuspEM1Eq-preservesEquiv G X m n =
  →∙pathToEquivPreserves' m (EM-raw∙≡CommSuspEM1 G n)
