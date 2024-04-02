{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Woset.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Order.StrictPoset.Base

open import Cubical.Induction.WellFounded

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isWoset→isStrictPoset : IsWoset R → IsStrictPoset R
  isWoset→isStrictPoset wos = isstrictposet
                              (IsWoset.is-set wos)
                              (IsWoset.is-prop-valued wos)
                              irrefl
                              (IsWoset.is-trans wos)
                              (isIrrefl×isTrans→isAsym R
                                (irrefl , (IsWoset.is-trans wos)))
                        where irrefl : isIrrefl R
                              irrefl = WellFounded→isIrrefl R
                                       (IsWoset.is-well-founded wos)

Woset→StrictPoset : Woset ℓ ℓ' → StrictPoset ℓ ℓ'
Woset→StrictPoset (_ , wos) = _ , strictposetstr (WosetStr._≺_ wos)
                                  (isWoset→isStrictPoset (WosetStr.isWoset wos))
