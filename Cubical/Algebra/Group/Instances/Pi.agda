module Cubical.Algebra.Group.Instances.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms

open IsGroup
open GroupStr
open IsMonoid
open IsSemigroup

module _ {ℓ ℓ' : Level} {X : Type ℓ} (G : X → Group ℓ') where
  ΠGroup : Group (ℓ-max ℓ ℓ')
  fst ΠGroup = (x : X) → fst (G x)
  1g (snd ΠGroup) x = 1g (G x .snd)
  GroupStr._·_ (snd ΠGroup) f g x = GroupStr._·_ (G x .snd) (f x) (g x)
  inv (snd ΠGroup) f x = inv (G x .snd) (f x)
  is-set (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) =
    isSetΠ λ x → is-set (G x .snd)
  IsSemigroup.·Assoc (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) f g h =
    funExt λ x → IsSemigroup.·Assoc (isSemigroup (isMonoid (G x .snd))) (f x) (g x) (h x)
  IsMonoid.·IdR (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → IsMonoid.·IdR (isMonoid (isGroup (snd (G x)))) (f x)
  IsMonoid.·IdL (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → IsMonoid.·IdL (isMonoid (isGroup (snd (G x)))) (f x)
  ·InvR (isGroup (snd ΠGroup)) f =
    funExt λ x → ·InvR (isGroup (snd (G x))) (f x)
  ·InvL (isGroup (snd ΠGroup)) f =
    funExt λ x → ·InvL (isGroup (snd (G x))) (f x)

ΠGroupHom : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {G : A → Group ℓ'} {H : A → Group ℓ''}
  → ((a : _) → GroupHom (G a) (H a))
  → GroupHom (ΠGroup G) (ΠGroup H)
fst (ΠGroupHom fam) f a = fst (fam a) (f a)
snd (ΠGroupHom fam) =
  makeIsGroupHom λ f g
    → funExt λ a → IsGroupHom.pres· (snd (fam a)) _ _

ΠGroupIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {G : A → Group ℓ'} {H : A → Group ℓ''}
  → ((a : _) → GroupIso (G a) (H a))
  → GroupIso (ΠGroup G) (ΠGroup H)
Iso.fun (fst (ΠGroupIso fam)) = fst (ΠGroupHom λ a → GroupIso→GroupHom (fam a))
Iso.inv (fst (ΠGroupIso fam)) =
  fst (ΠGroupHom λ a → GroupIso→GroupHom (invGroupIso (fam a)))
Iso.rightInv (fst (ΠGroupIso fam)) f = funExt λ x → Iso.rightInv (fst (fam x)) _
Iso.leftInv (fst (ΠGroupIso fam)) f = funExt λ x → Iso.leftInv (fst (fam x)) _
snd (ΠGroupIso fam) = snd (ΠGroupHom λ a → GroupIso→GroupHom (fam a))
