module Cubical.Relation.Binary.Order.Woset.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Woset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base

open import Cubical.Induction.WellFounded

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isWoset→isQuoset : IsWoset R → IsQuoset R
  isWoset→isQuoset wos = isquoset
                        (IsWoset.is-set wos)
                        (IsWoset.is-prop-valued wos)
                         irrefl
                        (IsWoset.is-trans wos)
                        (isIrrefl×isTrans→isAsym R
                          (irrefl , (IsWoset.is-trans wos)))
                   where irrefl : isIrrefl R
                         irrefl = WellFounded→isIrrefl R
                                 (IsWoset.is-well-founded wos)

Woset→Quoset : Woset ℓ ℓ' → Quoset ℓ ℓ'
Woset→Quoset (_ , wos) = _ , quosetstr (WosetStr._≺_ wos)
                            (isWoset→isQuoset (WosetStr.isWoset wos))
