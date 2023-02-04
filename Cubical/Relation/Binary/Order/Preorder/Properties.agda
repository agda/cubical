{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Preorder.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
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

  isPreorder→isEquivRelSymKernel : IsPreorder R → isEquivRel (SymKernel R)
  isPreorder→isEquivRelSymKernel preorder
    = equivRel (λ a → (IsPreorder.is-refl preorder a)
                    , (IsPreorder.is-refl preorder a))
               (isSymSymKernel R)
               (λ a b c (Rab , Rba) (Rbc , Rcb)
                 → IsPreorder.is-trans preorder a b c Rab Rbc
                 , IsPreorder.is-trans preorder c b a Rcb Rba)

  isPreorder→isStrictPosetAsymKernel : IsPreorder R → IsStrictPoset (AsymKernel R)
  isPreorder→isStrictPosetAsymKernel preorder
    = isstrictposet (IsPreorder.is-set preorder)
                    (λ a b → isProp× (IsPreorder.is-prop-valued preorder a b) (isProp¬ (R b a)))
                    (λ a (Raa , ¬Raa) → ¬Raa (IsPreorder.is-refl preorder a))
                    (λ a b c (Rab , ¬Rba) (Rbc , ¬Rcb)
                      → IsPreorder.is-trans preorder a b c Rab Rbc
                      , λ Rca → ¬Rcb (IsPreorder.is-trans preorder c a b Rca Rab))
                    (isAsymAsymKernel R)

Preorder→StrictPoset : Preorder ℓ ℓ' → StrictPoset ℓ ℓ'
Preorder→StrictPoset (_ , pre)
  = _ , strictposetstr (BinaryRelation.AsymKernel (PreorderStr._≲_ pre))
                       (isPreorder→isStrictPosetAsymKernel (PreorderStr.isPreorder pre))
