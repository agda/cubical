{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.TrivialGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties

open GroupStr
open GroupIso
open GroupHom

private
  variable
    ℓ : Level

trivialGroup : Group₀
trivialGroup = Unit , groupstr tt (λ _ _ → tt) (λ _ → tt)
                      (makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                                   (λ _ → refl) (λ _ → refl))

-- The trivial group is a unit.
lUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupIso (dirProd trivialGroup G) G
fun (map lUnitGroupIso) = snd
isHom (map lUnitGroupIso) _ _ = refl
inv lUnitGroupIso g = tt , g
rightInv lUnitGroupIso _ = refl
leftInv lUnitGroupIso _ = refl

rUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupIso (dirProd G trivialGroup) G
fun (map rUnitGroupIso) = fst
isHom (map rUnitGroupIso) _ _ = refl
inv rUnitGroupIso g = g , tt
rightInv rUnitGroupIso _ = refl
leftInv rUnitGroupIso _ = refl

lUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd trivialGroup G) G
lUnitGroupEquiv = GrIsoToGrEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd G trivialGroup) G
rUnitGroupEquiv = GrIsoToGrEquiv rUnitGroupIso

IsoContrGroupTrivialGroup : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupIso G trivialGroup
fun (map (IsoContrGroupTrivialGroup contr)) _ = tt
isHom (map (IsoContrGroupTrivialGroup contr)) _ _ = refl
inv (IsoContrGroupTrivialGroup contr) x = fst contr
rightInv (IsoContrGroupTrivialGroup contr) x = refl
leftInv (IsoContrGroupTrivialGroup contr) x = snd contr x

contrGroup≅trivialGroup : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupEquiv G trivialGroup
contrGroup≅trivialGroup contr = GrIsoToGrEquiv (IsoContrGroupTrivialGroup contr)
