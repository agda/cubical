{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Bool renaming (Bool to BoolType)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sum hiding (map ; rec)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Relation.Nullary

open GroupStr
open IsGroup
open IsMonoid
open IsSemigroup renaming (assoc to assoc')

Bool : Group₀
fst Bool = BoolType
1g (snd Bool) = true
(snd Bool GroupStr.· false) false = true
(snd Bool GroupStr.· false) true = false
(snd Bool GroupStr.· true) y = y
(inv (snd Bool)) x = x
is-set (isSemigroup (isMonoid (isGroup (snd Bool)))) = isSetBool
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) false false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) false false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) false true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) false true true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) true false false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) true false true = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) true true false = refl
assoc' (isSemigroup (isMonoid (isGroup (snd Bool)))) true true true = refl
identity (IsGroup.isMonoid (isGroup (snd Bool))) false = refl , refl
identity (IsGroup.isMonoid (isGroup (snd Bool))) true = refl , refl
inverse (isGroup (snd Bool)) false = refl , refl
inverse (isGroup (snd Bool)) true = refl , refl



-- Proof that any Group equivalent to Bool as types is also isomorphic to Bool as groups.
open GroupStr renaming (assoc to assocG)

module _ {ℓ : Level} {A : Group ℓ} (e : Iso (fst A) BoolType) where
  private
    discreteA : Discrete (typ A)
    discreteA = IsoPresDiscrete (invIso e) _≟_

    _·A_ = GroupStr._·_ (snd A)
    -A_ = GroupStr.inv (snd A)

    IsoABool : Iso BoolType (typ A)
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
    ... | no p  | no q  = inr (⊥-rec (q (sym (Iso.rightInv IsoABool x)
                                   ∙∙ cong (Iso.fun IsoABool) (¬false→true _ p)
                                   ∙∙ true→1)))
    ... | no p  | yes q = inl q

  ≅Bool : GroupIso Bool A
  ≅Bool .fst = IsoABool
  ≅Bool .snd = makeIsGroupHom homHelp
    where
    homHelp : _
    homHelp false false with discreteA (Iso.fun IsoABool false) (1g (snd A))
                           | (decA ((Iso.fun IsoABool false) ·A Iso.fun IsoABool false))
    ... | yes p | _     = true→1 ∙∙ sym (GroupStr.rid (snd A) (1g (snd A))) ∙∙ cong₂ (_·A_) (sym p) (sym p)
    ... | no p  | inl x = true→1 ∙ sym x
    ... | no p  | inr x = true→1 ∙∙ sym (helper _ x) ∙∙ sym x
      where
      helper : (x : typ A) → x ·A x ≡ x → x ≡ (1g (snd A))
      helper x p = sym (GroupStr.rid (snd A) x)
                ∙∙ cong (x ·A_) (sym (inverse (snd A) x .fst))
                ∙∙ assocG (snd A) x x (-A x) ∙∙ cong (_·A (-A x)) p
                ∙∙ inverse (snd A) x .fst
    homHelp false true = sym (GroupStr.rid (snd A) _) ∙ cong (Iso.fun IsoABool false ·A_) (sym true→1)
    homHelp true y = sym (GroupStr.lid (snd A) _) ∙ cong (_·A (Iso.fun IsoABool y)) (sym true→1)
