{-# OPTIONS --cubical --no-import-sorts --safe #-}
{-
Constructions of "sets" in the cumulative hierarchy. Including:
- the empty set
- unions
- ω
- replacement
- separation
-}

module Cubical.HITs.CumulativeHierarchy.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic as L hiding (_∈_; _⊆_; ⊆-refl)
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E hiding (elim)
open import Cubical.HITs.PropositionalTruncation as P hiding (elim; elim2)

open import Cubical.HITs.CumulativeHierarchy.Base
open import Cubical.HITs.CumulativeHierarchy.Properties
import Cubical.HITs.PropositionalTruncation.Monad as PropMonad

private
  variable
    ℓ ℓ' : Level

------------
-- Structures for building specific sets by giving encodings and decodings for their membership
-----------

record SetStructure ℓ : Type (ℓ-suc ℓ) where
  field
    X : Type ℓ
    ix : X → V ℓ
  resSet : V ℓ
  resSet = sett X ix

record SetPackage ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    structure : SetStructure ℓ
  open SetStructure structure hiding (resSet)
  open SetStructure structure using (resSet) public
  field
    ∈-rep : V ℓ → hProp ℓ'
    unpack : (x : X) → [ ∈-rep (ix x) ]
    repack : {y : V ℓ} → [ ∈-rep y ] → ∥ fiber ix y ∥

  classification : [ ∀[ y ] (y ∈ₛ resSet ⇔ ∈-rep y) ]
  classification y = intoClassifier , fromClassifier where
    intoClassifier : [ y ∈ₛ resSet ] → [ ∈-rep y ]
    intoClassifier (yi , yr) = P.rec (∈-rep y .snd) (λ { (x , ix) → subst (fst ∘ ∈-rep) ix (unpack x) }) y∈ where
      y∈ : [ y ∈ resSet ]
      y∈ = ∈∈ₛ {a = y} {b = resSet} .snd (yi , yr)
    fromClassifier : [ ∈-rep y ] → [ y ∈ₛ resSet ]
    fromClassifier yr = ∈∈ₛ {a = y} {b = resSet} .fst (repack {y = y} yr)

------------
-- Specific constructions
-----------
open SetPackage using (structure; ∈-rep; unpack; repack)

module EmptySet where
  EmptyStructure : SetStructure ℓ
  SetStructure.X EmptyStructure = Lift E.⊥
  SetStructure.ix EmptyStructure ()

  EmptyPackage : SetPackage ℓ ℓ-zero
  structure EmptyPackage = EmptyStructure
  ∈-rep EmptyPackage _ = L.⊥
  unpack EmptyPackage ()
  repack EmptyPackage ()

  ∅ : V ℓ
  ∅ = SetStructure.resSet EmptyStructure

  ∅-empty : [ ∀[ b ∶ V ℓ ] ¬ (b ∈ₛ ∅) ]
  ∅-empty b = SetPackage.classification EmptyPackage b .fst
open EmptySet using (∅; ∅-empty) public

module UnionSet (S : V ℓ) where
  UnionStructure : SetStructure ℓ
  SetStructure.X UnionStructure = Σ[ r ∈ ⟪ S ⟫ ] ⟪ ⟪ S ⟫↪ r ⟫
  SetStructure.ix UnionStructure (r , i) = ⟪ ⟪ S ⟫↪ r ⟫↪ i

  UNION : V ℓ
  UNION = SetStructure.resSet UnionStructure

  UnionPackage : SetPackage _ (ℓ-suc ℓ)
  structure UnionPackage = UnionStructure
  ∈-rep UnionPackage y = ∃[ v ] (v ∈ₛ S) ⊓ (y ∈ₛ v)
  unpack UnionPackage (vi , yi) = ∣ ⟪ S ⟫↪ vi , ∈ₛ⟪ S ⟫↪ vi , ∈ₛ⟪ ⟪ S ⟫↪ vi ⟫↪ yi ∣
  repack UnionPackage {y = y} = P.rec squash go where
    go : Σ[ v ∈ V _ ] [ v ∈ₛ S ] ⊓′ [ y ∈ₛ v ] → ∥ fiber _ y ∥
    go (v , (vi , vS) , xv) = ∣ repFiber≃fiber _ _ .fst ((vi , key .fst) , key .snd) ∣ where
      path : v ≡ ⟪ S ⟫↪ vi
      path = sym (equivFun identityPrinciple vS)
      key : Σ[ i ∈ ⟪ ⟪ S ⟫↪ vi ⟫ ] ⟪ ⟪ S ⟫↪ vi ⟫↪ i ≊ y
      key = subst (λ v → Σ[ ix ∈ ⟪ v ⟫ ] ⟪ v ⟫↪ ix ≊ y) path xv

  union-ax : [ ∀[ u ] (u ∈ₛ UNION ⇔ (∃[ v ] (v ∈ₛ S) ⊓ (u ∈ₛ v))) ]
  union-ax u = classification u .fst , classification u .snd where
    open SetPackage UnionPackage using (classification)
open UnionSet renaming (UNION to infixr 9 ⋃_) using (union-ax) public

module PairingSet (a b : V ℓ) where
  PairingStructure : SetStructure ℓ
  SetStructure.X PairingStructure = Lift Bool
  SetStructure.ix PairingStructure (lift false) = a
  SetStructure.ix PairingStructure (lift true) = b

  PairingPackage : SetPackage _ (ℓ-suc ℓ)
  structure PairingPackage = PairingStructure
  ∈-rep PairingPackage d = (d ≡ₕ a) ⊔ (d ≡ₕ b)
  unpack PairingPackage (lift false) = L.inl refl
  unpack PairingPackage (lift true) = L.inr refl
  repack PairingPackage {y = y} = P.rec squash λ { (_⊎_.inl ya) → ∣ lift false , sym ya ∣ ; (_⊎_.inr yb) → ∣ lift true , sym yb ∣ }

  PAIR : V ℓ
  PAIR = SetStructure.resSet PairingStructure

  pairing-ax : [ ∀[ d ] (d ∈ₛ PAIR ⇔ (d ≡ₕ a) ⊔ (d ≡ₕ b)) ]
  pairing-ax d = classification d .fst , classification d .snd where
    open SetPackage PairingPackage using (classification)
-- pairing TODO: notation?
open PairingSet renaming (PAIR to infix 12 ⁅_,_⁆) using (pairing-ax) public

module SingletonSet (a : V ℓ) where
  SingletonStructure : SetStructure ℓ
  SetStructure.X SingletonStructure = Lift Unit
  SetStructure.ix SingletonStructure (lift tt) = a

  SingletonPackage : SetPackage _ (ℓ-suc ℓ)
  structure SingletonPackage = SingletonStructure
  ∈-rep SingletonPackage d = d ≡ₕ a
  unpack SingletonPackage _ = refl
  repack SingletonPackage ya = ∣ lift tt , sym ya ∣

  SINGL : V ℓ
  SINGL = SetStructure.resSet SingletonStructure
open SingletonSet renaming (SINGL to infix 10 ⁅_⁆s) public

-- small unions
_∪_ : (a b : V ℓ) → V ℓ
a ∪ b = ⋃ ⁅ a , b ⁆

module InfinitySet {ℓ} where
  #_ : ℕ → V ℓ
  # zero = ∅
  # suc n = (# n) ∪ ⁅ # n ⁆s

  ωStructure : SetStructure ℓ
  SetStructure.X ωStructure = Lift ℕ
  SetStructure.ix ωStructure = #_ ∘ lower

  ω : V ℓ
  ω = SetStructure.resSet ωStructure

  open PropMonad
  ωPackage : SetPackage _ (ℓ-suc ℓ)
  structure ωPackage = ωStructure
  ∈-rep ωPackage d = (d ≡ₕ ∅) ⊔ (∃[ v ] (d ≡ₕ v ∪ ⁅ v ⁆s) ⊓ (v ∈ₛ ω))
  unpack ωPackage (lift zero) = L.inl refl
  unpack ωPackage (lift (suc n)) = L.inr ∣ # n , refl , ∈∈ₛ {b = ω} .fst ∣ lift n , refl ∣ ∣
  repack ωPackage {y = y} = ⊔-elim (y ≡ₕ ∅) ∥ _ ∥ₚ (λ _ → ∥ fiber _ y ∥ₚ)
    (λ e → ∣ lift zero , sym e ∣)
    (λ m → do (v , yv , vr) ← m
              (lift n , eq) ← ∈∈ₛ {b = ω} .snd vr
              ∣ lift (suc n) , sym (subst (λ v → y ≡ (v ∪ ⁅ v ⁆s)) (sym eq) yv) ∣
    )

  ω-empty : [ ∅ ∈ₛ ω ]
  ω-empty = SetPackage.classification ωPackage ∅ .snd (L.inl refl)

  ω-next : [ ∀[ x ∶ V ℓ ] x ∈ₛ ω ⇒ (x ∪ ⁅ x ⁆s) ∈ₛ ω ]
  ω-next x x∈ω = SetPackage.classification ωPackage (x ∪ ⁅ x ⁆s) .snd (L.inr ∣ x , refl , x∈ω ∣)
open InfinitySet using (ω; ω-empty; ω-next) public

module ReplacementSet (r : V ℓ → V ℓ) (a : V ℓ) where
  ReplacementStructure : SetStructure ℓ
  SetStructure.X ReplacementStructure = ⟪ a ⟫
  SetStructure.ix ReplacementStructure = r ∘ ⟪ a ⟫↪

  REPLACED : V ℓ
  REPLACED = SetStructure.resSet ReplacementStructure

  open PropMonad
  ReplacementPackage : SetPackage _ (ℓ-suc ℓ)
  structure ReplacementPackage = ReplacementStructure
  ∈-rep ReplacementPackage y = ∃[ z ] (z ∈ₛ a) ⊓ (y ≡ₕ r z)
  unpack ReplacementPackage ⟪a⟫ = ∣ ⟪ a ⟫↪ ⟪a⟫ , (∈ₛ⟪ a ⟫↪ ⟪a⟫) , refl ∣
  repack ReplacementPackage {y = y} m = do
    (z , (a , za) , yr) ← m
    ∣ a , cong r (equivFun identityPrinciple za) ∙ sym yr ∣

  replacement-ax : [ ∀[ y ] (y ∈ₛ REPLACED ⇔ (∃[ z ] (z ∈ₛ a) ⊓ (y ≡ₕ r z))) ]
  replacement-ax y = classification y .fst , classification y .snd where
    open SetPackage ReplacementPackage using (classification)
open ReplacementSet renaming (REPLACED to infix 12 ⁅_∣_⁆) using (replacement-ax) public

module SeparationSet (a : V ℓ) (ϕ : V ℓ → hProp ℓ) where
  SeparationStructure : SetStructure ℓ
  SetStructure.X SeparationStructure = Σ[ x ∈ ⟪ a ⟫ ] [ ϕ (⟪ a ⟫↪ x) ]
  SetStructure.ix SeparationStructure = ⟪ a ⟫↪ ∘ fst

  SeparationPackage : SetPackage _ ℓ
  structure SeparationPackage = SeparationStructure
  ∈-rep SeparationPackage y = (y ∈ₛ a) ⊓ ϕ y
  unpack SeparationPackage (⟪a⟫ , phi) = (∈ₛ⟪ a ⟫↪ ⟪a⟫) , phi
  repack SeparationPackage ((⟪a⟫ , ya) , phi) = ∣ (⟪a⟫ , subst (fst ∘ ϕ) (sym (equivFun identityPrinciple ya)) phi) , equivFun identityPrinciple ya ∣

  SEPAREE : V ℓ
  SEPAREE = SetStructure.resSet SeparationStructure

  separation-ax : [ ∀[ y ] (y ∈ₛ SEPAREE ⇔ (y ∈ₛ a) ⊓ ϕ y) ]
  separation-ax y = classification y .fst , classification y .snd where
    open SetPackage SeparationPackage using (classification)
open SeparationSet renaming (SEPAREE to infix 12 ⁅_∶_⁆) using (separation-ax) public
