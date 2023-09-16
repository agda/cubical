{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Toset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

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

  isToset→isPoset : IsToset R → IsPoset R
  isToset→isPoset toset = isposet
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

  isToset→isLosetIrreflKernel : Discrete A → IsToset R → IsLoset (IrreflKernel R)
  isToset→isLosetIrreflKernel disc toset
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

  isTosetInduced : IsToset R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsToset (InducedRelation R (B , f))
  isTosetInduced tos B (f , emb)
    = istoset (Embedding-into-isSet→isSet (f , emb) (IsToset.is-set tos))
              (λ a b → IsToset.is-prop-valued tos (f a) (f b))
              (λ a → IsToset.is-refl tos (f a))
              (λ a b c → IsToset.is-trans tos (f a) (f b) (f c))
              (λ a b a≤b b≤a → isEmbedding→Inj emb a b
                (IsToset.is-antisym tos (f a) (f b) a≤b b≤a))
              λ a b → IsToset.is-strongly-connected tos (f a) (f b)

Toset→Poset : Toset ℓ ℓ' → Poset ℓ ℓ'
Toset→Poset (_ , tos) = _ , posetstr (TosetStr._≤_ tos)
                                     (isToset→isPoset (TosetStr.isToset tos))

Toset→Loset : (tos : Toset ℓ ℓ') → Discrete (fst tos) → Loset ℓ (ℓ-max ℓ ℓ')
Toset→Loset (_ , tos) disc
  = _ , losetstr (BinaryRelation.IrreflKernel (TosetStr._≤_ tos))
                       (isToset→isLosetIrreflKernel disc
                                                    (TosetStr.isToset tos))
