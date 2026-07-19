module Cubical.Algebra.Group.Instances.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum hiding (map ; rec)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open GroupStr
open IsGroup
open IsMonoid
open IsSemigroup



BoolGroup : Group₀
fst BoolGroup = Bool
1g (snd BoolGroup) = true
(snd BoolGroup · false) false = true
(snd BoolGroup · false) true = false
(snd BoolGroup · true) y = y
inv (snd BoolGroup) x = x
is-set (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) = isSetBool
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false false = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false true = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true false = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true true = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false false = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false true = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true false = refl
·Assoc (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true true = refl
·IdR (isMonoid (isGroup (snd BoolGroup))) false = refl
·IdR (isMonoid (isGroup (snd BoolGroup))) true = refl
·IdL (isMonoid (isGroup (snd BoolGroup))) false = refl
·IdL (isMonoid (isGroup (snd BoolGroup))) true = refl
·InvR (isGroup (snd BoolGroup)) false = refl
·InvR (isGroup (snd BoolGroup)) true = refl
·InvL (isGroup (snd BoolGroup)) false = refl
·InvL (isGroup (snd BoolGroup)) true = refl

-- Proof that any Group equivalent to Bool as types is also isomorphic to Bool as groups.
open GroupStr renaming (·Assoc to ·AssocG)

module _ {ℓ : Level} {A : Group ℓ} (e : Iso (fst A) Bool) where
  private
    discreteA : Discrete (typ A)
    discreteA = isoPresDiscrete (invIso e) _≟_

    _·A_ = GroupStr._·_ (snd A)
    -A_ = GroupStr.inv (snd A)

    IsoABool : Iso Bool (typ A)
    IsoABool with (Iso.fun e (1g (snd A))) ≟ true
    ... | yes p = invIso e
    ... | no p = compIso notIso (invIso e)

    true→1 : Iso.fun IsoABool true ≡ 1g (snd A)
    true→1 with (Iso.fun e (1g (snd A))) ≟ true
    ... | yes p = sym (cong (Iso.inv e) p) ∙ Iso.leftInv e _
    ... | no p = sym (cong (Iso.inv e) (¬true→false (Iso.fun e (1g (snd A))) p))
               ∙ Iso.leftInv e (1g (snd A))

    decA : (x : typ A) → (x ≡ 1g (snd A)) ⊎ (x ≡ Iso.fun IsoABool false)
    decA x with (Iso.inv IsoABool x) ≟ false | discreteA x (1g (snd A))
    ... | yes p | yes q = inl q
    ... | yes p | no q  = inr (sym (Iso.rightInv IsoABool x) ∙ cong (Iso.fun (IsoABool)) p)
    ... | no p  | no q  = inr (⊥.rec (q (sym (Iso.rightInv IsoABool x)
                                   ∙∙ cong (Iso.fun IsoABool) (¬false→true _ p)
                                   ∙∙ true→1)))
    ... | no p  | yes q = inl q

  ≅Bool : GroupIso BoolGroup A
  ≅Bool .fst = IsoABool
  ≅Bool .snd = makeIsGroupHom homHelp
    where
    homHelp : _
    homHelp false false with discreteA (Iso.fun IsoABool false) (1g (snd A))
                           | (decA ((Iso.fun IsoABool false) ·A Iso.fun IsoABool false))
    ... | yes p | _     = true→1 ∙∙ sym (GroupStr.·IdR (snd A) (1g (snd A))) ∙∙ cong₂ (_·A_) (sym p) (sym p)
    ... | no p  | inl x = true→1 ∙ sym x
    ... | no p  | inr x = true→1 ∙∙ sym (helper _ x) ∙∙ sym x
      where
      helper : (x : typ A) → x ·A x ≡ x → x ≡ (1g (snd A))
      helper x p = sym (GroupStr.·IdR (snd A) x)
                ∙∙ cong (x ·A_) (sym ((snd A) .·InvR x))
                ∙∙ ·AssocG (snd A) x x (-A x) ∙∙ cong (_·A (-A x)) p
                ∙∙ (snd A) .·InvR x
    homHelp false true = sym (GroupStr.·IdR (snd A) _) ∙ cong (Iso.fun IsoABool false ·A_) (sym true→1)
    homHelp true y = sym (GroupStr.·IdL (snd A) _) ∙ cong (_·A (Iso.fun IsoABool y)) (sym true→1)
