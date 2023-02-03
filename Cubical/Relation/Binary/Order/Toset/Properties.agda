{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Toset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Toset.Base
open import Cubical.Relation.Binary.Order.Loset.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isToset→IsPoset : IsToset R → IsPoset R
  isToset→IsPoset toset = isposet
                          (IsToset.is-set toset)
                          (IsToset.is-prop-valued toset)
                          (IsToset.is-refl toset)
                          (IsToset.is-trans toset)
                          (IsToset.is-antisym toset)
  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isToset→IsLosetIrreflKernel : Discrete A → IsToset R → IsLoset (IrreflKernel R)
  isToset→IsLosetIrreflKernel disc toset
    = isloset (IsToset.is-set toset)
              (λ a b → isProp× (IsToset.is-prop-valued toset a b)
                               (isProp¬ (a ≡ b)))
              (isIrreflIrreflKernel R)
              (transirrefl (IsToset.is-trans toset)
                           (IsToset.is-antisym toset))
              (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                       (isIrreflIrreflKernel R
                                       , transirrefl (IsToset.is-trans toset)
                                                     (IsToset.is-antisym toset)))
              (λ a c b (Rac , ¬a≡c)
                → decRec (λ a≡b → ∥₁.map (⊎.rec
                         (λ Rbc → inr (Rbc , λ b≡c → ¬a≡c (a≡b ∙ b≡c)))
                                λ Rcb → ⊥.rec (¬a≡c (IsToset.is-antisym toset a c Rac
                                              (subst (λ x → R c x) (sym a≡b) Rcb))))
                                  (IsToset.is-strongly-connected toset b c))
                         (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → Rab , ¬a≡b)
                                   (λ Rba → (IsToset.is-trans toset b a c Rba Rac)
                                   , λ b≡c → ¬a≡b (IsToset.is-antisym toset a b
                                       (subst (λ x → R a x) (sym b≡c) Rac) Rba)))
                                 (IsToset.is-strongly-connected toset a b))
                         (disc a b))
              (isConnectedStronglyConnectedIrreflKernel R
                (IsToset.is-strongly-connected toset))

Toset→Poset : Toset ℓ ℓ' → Poset ℓ ℓ'
Toset→Poset (_ , tos) = _ , posetstr (TosetStr._≤_ tos)
                                     (isToset→IsPoset (TosetStr.isToset tos))

Toset→Loset : (tos : Toset ℓ ℓ') → Discrete (fst tos) → Loset ℓ (ℓ-max ℓ ℓ')
Toset→Loset (_ , tos) disc
  = _ , losetstr (BinaryRelation.IrreflKernel (TosetStr._≤_ tos))
                       (isToset→IsLosetIrreflKernel disc
                                                    (TosetStr.isToset tos))
