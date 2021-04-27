{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum hiding (map ; rec)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Relation.Nullary


open GroupStr
open IsGroup
open IsMonoid
open IsSemigroup renaming (assoc to assoc')

BoolGroup : Group₀
fst BoolGroup = Bool
0g (snd BoolGroup) = true
(snd BoolGroup GroupStr.+ false) false = true
(snd BoolGroup GroupStr.+ false) true = false
(snd BoolGroup GroupStr.+ true) y = y
(- snd BoolGroup) false = false
(- snd BoolGroup) true = true
is-set (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) = isSetBool
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) false true true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd BoolGroup)))) true true true = refl
identity (IsGroup.isMonoid (isGroup (snd BoolGroup))) false = refl , refl
identity (IsGroup.isMonoid (isGroup (snd BoolGroup))) true = refl , refl
inverse (isGroup (snd BoolGroup)) false = refl , refl
inverse (isGroup (snd BoolGroup)) true = refl , refl



-- Proof that any Group equivalent to Bool as types is also isomorhic to Bool as groups.
open GroupStr renaming (assoc to assocG)

module _ {ℓ : Level} {A : Group {ℓ}} (e : Iso (fst A) Bool) where
  private
    discreteA : Discrete (typ A)
    discreteA = IsoPresDiscrete (invIso e) _≟_

    _+A_ = GroupStr._+_ (snd A)
    -A_ = GroupStr.-_ (snd A)

    notIso : Iso Bool Bool
    Iso.fun notIso = not
    Iso.inv notIso = not
    Iso.rightInv notIso = notnot
    Iso.leftInv notIso = notnot

    ¬true→false : (x : Bool) → ¬ x ≡ true → x ≡ false
    ¬true→false false _ = refl
    ¬true→false true p = ⊥-rec (p refl)

    ¬false→true : (x : Bool) → ¬ x ≡ false → x ≡ true
    ¬false→true false p = ⊥-rec (p refl)
    ¬false→true true _ = refl

    IsoABool : Iso Bool (typ A)
    IsoABool with (Iso.fun e (0g (snd A))) ≟ true
    ... | yes p = invIso e
    ... | no p = compIso notIso (invIso e)

    true→0 : Iso.fun IsoABool true ≡ 0g (snd A)
    true→0 with (Iso.fun e (0g (snd A))) ≟ true
    ... | yes p = sym (cong (Iso.inv e) p) ∙ Iso.leftInv e _
    ... | no p = sym (cong (Iso.inv e) (¬true→false (Iso.fun e (0g (snd A))) p))
               ∙ Iso.leftInv e (0g (snd A))

    decA : (x : typ A) → (x ≡ 0g (snd A)) ⊎ (x ≡ Iso.fun IsoABool false)
    decA x with (Iso.inv IsoABool x) ≟ false | discreteA x (0g (snd A))
    ... | yes p | yes q = inl q
    ... | yes p | no q  = inr (sym (Iso.rightInv IsoABool x) ∙ cong (Iso.fun (IsoABool)) p)
    ... | no p  | no q  = inr (⊥-rec (q (sym (Iso.rightInv IsoABool x)
                                   ∙∙ cong (Iso.fun IsoABool) (¬false→true _ p)
                                   ∙∙ true→0)))
    ... | no p  | yes q = inl q

  ≅Bool : GroupIso BoolGroup A
  ≅Bool = Iso+Hom→GrIso IsoABool homHelp
    where
    homHelp : isGroupHom BoolGroup A (Iso.fun IsoABool)
    homHelp false false with discreteA (Iso.fun IsoABool false) (0g (snd A))
                           | (decA ((Iso.fun IsoABool false) +A Iso.fun IsoABool false))
    ... | yes p | _     = true→0 ∙∙ sym (GroupStr.rid (snd A) (0g (snd A))) ∙∙ cong₂ (_+A_) (sym p) (sym p)
    ... | no p  | inl x = true→0 ∙ sym x
    ... | no p  | inr x = true→0 ∙∙ sym (helper _ x) ∙∙ sym x
      where
      helper : (x : typ A) → x +A x ≡ x → x ≡ (0g (snd A))
      helper x p = sym (GroupStr.rid (snd A) x)
                ∙∙ cong (x +A_) (sym (inverse (snd A) x .fst))
                ∙∙ assocG (snd A) x x (-A x) ∙∙ cong (_+A (-A x)) p
                ∙∙ inverse (snd A) x .fst
    homHelp false true = sym (GroupStr.rid (snd A) _) ∙ cong (Iso.fun IsoABool false +A_) (sym true→0)
    homHelp true y = sym (GroupStr.lid (snd A) _) ∙ cong (_+A (Iso.fun IsoABool y)) (sym true→0)
