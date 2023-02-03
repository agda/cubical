{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Preorder.Base
open import Cubical.Relation.Binary.Order.StrictPoset.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→IsPreorder : IsPoset R → IsPreorder R
  isPoset→IsPreorder poset = ispreorder
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isPoset→IsStrictPosetIrreflKernel : IsPoset R → IsStrictPoset (IrreflKernel R)
  isPoset→IsStrictPosetIrreflKernel poset
    = isstrictposet (IsPoset.is-set poset)
                    (λ a b → isProp× (IsPoset.is-prop-valued poset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsPoset.is-trans poset)
                                 (IsPoset.is-antisym poset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsPoset.is-trans poset)
                                                           (IsPoset.is-antisym poset)))

Poset→Preorder : Poset ℓ ℓ' → Preorder ℓ ℓ'
Poset→Preorder (_ , pos) = _ , preorderstr (PosetStr._≤_ pos)
                                           (isPoset→IsPreorder (PosetStr.isPoset pos))

Poset→StrictPoset : Poset ℓ ℓ' → StrictPoset ℓ (ℓ-max ℓ ℓ')
Poset→StrictPoset (_ , pos)
  = _ , strictposetstr (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
                       (isPoset→IsStrictPosetIrreflKernel (PosetStr.isPoset pos))
