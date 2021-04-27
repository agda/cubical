{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit renaming (Unit to UnitType)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open GroupStr
open GroupIso
open GroupHom

private
  variable
    ℓ : Level

Unit : Group₀
Unit = UnitType , groupstr tt (λ _ _ → tt) (λ _ → tt)
                      (makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                                   (λ _ → refl) (λ _ → refl))

-- The trivial group is a unit.
lUnitGroupIso : {G : Group {ℓ}} → GroupIso (dirProd Unit G) G
fun (fun lUnitGroupIso) = snd
isHom (fun lUnitGroupIso) _ _ = refl
inv lUnitGroupIso g = tt , g
rightInv lUnitGroupIso _ = refl
leftInv lUnitGroupIso _ = refl

rUnitGroupIso : {G : Group {ℓ}} → GroupIso (dirProd G Unit) G
fun (fun rUnitGroupIso) = fst
isHom (fun rUnitGroupIso) _ _ = refl
inv rUnitGroupIso g = g , tt
rightInv rUnitGroupIso _ = refl
leftInv rUnitGroupIso _ = refl

lUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd Unit G) G
lUnitGroupEquiv = GrIsoToGrEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd G Unit) G
rUnitGroupEquiv = GrIsoToGrEquiv rUnitGroupIso

contrGroupIsoUnit : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupIso G Unit
fun (fun (contrGroupIsoUnit contr)) _ = tt
isHom (fun (contrGroupIsoUnit contr)) _ _ = refl
inv (contrGroupIsoUnit contr) x = fst contr
rightInv (contrGroupIsoUnit contr) x = refl
leftInv (contrGroupIsoUnit contr) x = snd contr x

contrGroupEquivUnit : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupEquiv G Unit
contrGroupEquivUnit contr = GrIsoToGrEquiv (contrGroupIsoUnit contr)
