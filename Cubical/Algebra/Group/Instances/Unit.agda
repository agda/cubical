{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit renaming (Unit to UnitType)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)
open import Cubical.Algebra.Group.GroupPath

open GroupStr
open IsGroupHom

private
  variable
    ℓ : Level

Unit : Group₀
Unit = UnitType , groupstr tt (λ _ _ → tt) (λ _ → tt)
                      (makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                                   (λ _ → refl) (λ _ → refl))

open Iso

-- The trivial group is a unit.
lUnitGroupIso : {G : Group ℓ} → GroupIso (DirProd Unit G) G
fun (fst lUnitGroupIso) = snd
inv (fst lUnitGroupIso) g = tt , g
rightInv (fst lUnitGroupIso) _ = refl
leftInv (fst lUnitGroupIso) _ = refl
snd lUnitGroupIso = makeIsGroupHom λ _ _ → refl

rUnitGroupIso : {G : Group ℓ} → GroupIso (DirProd G Unit) G
fun (fst rUnitGroupIso) = fst
inv (fst rUnitGroupIso) g = g , tt
rightInv (fst rUnitGroupIso) _ = refl
leftInv (fst rUnitGroupIso) _ = refl
snd rUnitGroupIso = makeIsGroupHom λ _ _ → refl

lUnitGroupEquiv : {G : Group ℓ} → GroupEquiv (DirProd Unit G) G
lUnitGroupEquiv = GroupIso→GroupEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group ℓ} → GroupEquiv (DirProd G Unit) G
rUnitGroupEquiv = GroupIso→GroupEquiv rUnitGroupIso

contrGroupIsoUnit : {G : Group ℓ} → isContr ⟨ G ⟩ → GroupIso G Unit
fun (fst (contrGroupIsoUnit contr)) _ = tt
inv (fst (contrGroupIsoUnit contr)) _ = fst contr
rightInv (fst (contrGroupIsoUnit contr)) _ = refl
leftInv (fst (contrGroupIsoUnit contr)) x = snd contr x
snd (contrGroupIsoUnit contr) = makeIsGroupHom λ _ _ → refl

contrGroupEquivUnit : {G : Group ℓ} → isContr ⟨ G ⟩ → GroupEquiv G Unit
contrGroupEquivUnit contr = GroupIso→GroupEquiv (contrGroupIsoUnit contr)

SES→isEquiv : ∀ {ℓ ℓ'} {L R : Group ℓ-zero}
  → {G : Group ℓ} {H : Group ℓ'}
  → Unit ≡ L
  → Unit ≡ R
  → (lhom : GroupHom L G) (midhom : GroupHom G H) (rhom : GroupHom H R)
  → ((x : _) → isInKer midhom x → isInIm lhom x)
  → ((x : _) → isInKer rhom x → isInIm midhom x)
  → isEquiv (fst midhom)
SES→isEquiv {R = R} {G = G} {H = H} =
  J (λ L _ → Unit ≡ R →
      (lhom : GroupHom L G) (midhom : GroupHom G H)
      (rhom : GroupHom H R) →
      ((x : fst G) → isInKer midhom x → isInIm lhom x) →
      ((x : fst H) → isInKer rhom x → isInIm midhom x) →
      isEquiv (fst midhom))
      ((J (λ R _ → (lhom : GroupHom Unit G) (midhom : GroupHom G H)
                   (rhom : GroupHom H R) →
                   ((x : fst G) → isInKer midhom x → isInIm lhom x) →
                   ((x : _) → isInKer rhom x → isInIm midhom x) →
                   isEquiv (fst midhom))
         main))
  where
  main : (lhom : GroupHom Unit G) (midhom : GroupHom G H)
         (rhom : GroupHom H Unit) →
         ((x : fst G) → isInKer midhom x → isInIm lhom x) →
         ((x : fst H) → isInKer rhom x → isInIm midhom x) →
         isEquiv (fst midhom)
  main lhom midhom rhom lexact rexact =
    BijectionIsoToGroupEquiv {G = G} {H = H}
      bijIso' .fst .snd
    where
    bijIso' : BijectionIso G H
    BijectionIso.fun bijIso' = midhom
    BijectionIso.inj bijIso' x inker =
      pRec (GroupStr.is-set (snd G) _ _)
           (λ s → sym (snd s) ∙ IsGroupHom.pres1 (snd lhom))
           (lexact _ inker)
    BijectionIso.surj bijIso' x = rexact x refl

isContr→≡UnitGroup : {G : Group ℓ-zero} → isContr (fst G) → Unit ≡ G
isContr→≡UnitGroup c =
  fst (GroupPath _ _)
    (invGroupEquiv ((isContr→≃Unit c)
                  , (makeIsGroupHom (λ _ _ → refl))))

GroupIsoUnitGroup→isContr : {G : Group ℓ-zero}
                           → GroupIso Unit G → isContr (fst G)
GroupIsoUnitGroup→isContr is =
  isOfHLevelRetractFromIso 0 (invIso (fst is)) isContrUnit
