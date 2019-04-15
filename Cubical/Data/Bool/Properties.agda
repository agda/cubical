{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Bool.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

notnot : ∀ x → not (not x) ≡ x
notnot true  = refl
notnot false = refl

notIsEquiv : isEquiv not
notIsEquiv = isoToIsEquiv (iso not not notnot notnot)

notEquiv : Bool ≃ Bool
notEquiv = (not , notIsEquiv)

notEq : Bool ≡ Bool
notEq = ua notEquiv

private
  -- This computes to false as expected
  nfalse : Bool
  nfalse = transp (λ i → notEq i) i0 true

  -- Sanity check
  nfalsepath : nfalse ≡ false
  nfalsepath = refl

isSetBool : isSet Bool
isSetBool = Discrete→isSet _≟_

true≢false : ¬ true ≡ false
true≢false p = subst (caseBool Bool ⊥) p true

false≢true : ¬ false ≡ true
false≢true p = subst (caseBool ⊥ Bool) p true

zeroˡ : ∀ x → true or x ≡ true
zeroˡ false = refl
zeroˡ true  = refl

zeroʳ : ∀ x → x or true ≡ true
zeroʳ false = refl
zeroʳ true  = refl

or-identityˡ : ∀ x → false or x ≡ x
or-identityˡ false = refl
or-identityˡ true  = refl

or-identityʳ : ∀ x → x or false ≡ x
or-identityʳ false = refl
or-identityʳ true  = refl

or-comm      : ∀ x y → x or y ≡ y or x
or-comm false y =
  false or y ≡⟨ or-identityˡ y ⟩
  y          ≡⟨ sym (or-identityʳ y) ⟩
  y or false ∎
or-comm true y =
  true or y ≡⟨ zeroˡ y ⟩
  true      ≡⟨ sym (zeroʳ y) ⟩
  y or true ∎

or-assoc     : ∀ x y z → x or (y or z) ≡ (x or y) or z
or-assoc false y z =
  false or (y or z)   ≡⟨ or-identityˡ _ ⟩
  y or z              ≡[ i ]⟨ or-identityˡ y (~ i) or z ⟩
  ((false or y) or z) ∎
or-assoc true y z  =
 true or (y or z)  ≡⟨ zeroˡ _ ⟩
  true             ≡⟨ sym (zeroˡ _) ⟩
  true or z        ≡[ i ]⟨ zeroˡ y (~ i) or z ⟩
  (true or y) or z ∎

or-idem      : ∀ x → x or x ≡ x
or-idem false = refl
or-idem true  = refl
