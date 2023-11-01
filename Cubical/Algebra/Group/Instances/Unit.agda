{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath

open GroupStr
open IsGroupHom

private
  variable
    ℓ : Level

UnitGroup₀ : Group₀
fst UnitGroup₀ = Unit
1g (snd UnitGroup₀) = tt
_·_ (snd UnitGroup₀) = λ _ _ → tt
inv (snd UnitGroup₀) = λ _ → tt
isGroup (snd UnitGroup₀) =
  makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                        (λ _ → refl) (λ _ → refl)

UnitGroup : Group ℓ
fst UnitGroup = Unit*
1g (snd UnitGroup) = tt*
_·_ (snd UnitGroup) = λ _ _ → tt*
inv (snd UnitGroup) = λ _ → tt*
isGroup (snd UnitGroup) =
  makeIsGroup (isOfHLevelUnit* 2)
              (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
              (λ _ → refl) (λ _ → refl)

open Iso

-- The trivial group is a unit.
lUnitGroupIso : {G : Group ℓ} → GroupIso (DirProd UnitGroup₀ G) G
fun (fst lUnitGroupIso) = snd
inv (fst lUnitGroupIso) g = tt , g
rightInv (fst lUnitGroupIso) _ = refl
leftInv (fst lUnitGroupIso) _ = refl
snd lUnitGroupIso = makeIsGroupHom λ _ _ → refl

rUnitGroupIso : {G : Group ℓ} → GroupIso (DirProd G UnitGroup₀) G
fun (fst rUnitGroupIso) = fst
inv (fst rUnitGroupIso) g = g , tt
rightInv (fst rUnitGroupIso) _ = refl
leftInv (fst rUnitGroupIso) _ = refl
snd rUnitGroupIso = makeIsGroupHom λ _ _ → refl

-- lifted version
lUnitGroupIso^ : ∀ {ℓ ℓ'} {G : Group ℓ'}
  → GroupIso (DirProd (UnitGroup {ℓ}) G) G
fun (fst lUnitGroupIso^) = snd
inv (fst lUnitGroupIso^) = tt* ,_
rightInv (fst lUnitGroupIso^) g = refl
leftInv (fst lUnitGroupIso^) (tt* , g) = refl
snd lUnitGroupIso^ = makeIsGroupHom λ _ _ → refl

rUnitGroupIso^ : ∀ {ℓ ℓ'} {G : Group ℓ'}
  → GroupIso (DirProd G (UnitGroup {ℓ})) G
fun (fst rUnitGroupIso^) = fst
inv (fst rUnitGroupIso^) = _, tt*
rightInv (fst rUnitGroupIso^) g = refl
leftInv (fst rUnitGroupIso^) (g , tt*) = refl
snd rUnitGroupIso^ = makeIsGroupHom λ _ _ → refl

lUnitGroupEquiv : {G : Group ℓ} → GroupEquiv (DirProd UnitGroup₀ G) G
lUnitGroupEquiv = GroupIso→GroupEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group ℓ} → GroupEquiv (DirProd G UnitGroup₀) G
rUnitGroupEquiv = GroupIso→GroupEquiv rUnitGroupIso

contrGroupIsoUnit : {G : Group ℓ} → isContr ⟨ G ⟩ → GroupIso G UnitGroup₀
fun (fst (contrGroupIsoUnit contr)) _ = tt
inv (fst (contrGroupIsoUnit contr)) _ = fst contr
rightInv (fst (contrGroupIsoUnit contr)) _ = refl
leftInv (fst (contrGroupIsoUnit contr)) x = snd contr x
snd (contrGroupIsoUnit contr) = makeIsGroupHom λ _ _ → refl

contrGroupEquivUnit : {G : Group ℓ} → isContr ⟨ G ⟩ → GroupEquiv G UnitGroup₀
contrGroupEquivUnit contr = GroupIso→GroupEquiv (contrGroupIsoUnit contr)

isContr→≡UnitGroup : {G : Group ℓ-zero} → isContr (fst G) → UnitGroup₀ ≡ G
isContr→≡UnitGroup c =
  fst (GroupPath _ _)
    (invGroupEquiv ((isContr→≃Unit c)
                  , (makeIsGroupHom (λ _ _ → refl))))

GroupIsoUnitGroup→isContr : {G : Group ℓ-zero}
                           → GroupIso UnitGroup₀ G → isContr (fst G)
GroupIsoUnitGroup→isContr is =
  isOfHLevelRetractFromIso 0 (invIso (fst is)) isContrUnit

→UnitHom : ∀ {ℓ} (G : Group ℓ) → GroupHom G UnitGroup₀
fst (→UnitHom G) _ = tt
snd (→UnitHom G) = makeIsGroupHom λ _ _ → refl
