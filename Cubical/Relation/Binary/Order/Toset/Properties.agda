{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Toset.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Proset.Properties
open import Cubical.Relation.Binary.Order.Poset
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

  isTosetDecidable→Discrete : IsToset R → isDecidable R → Discrete A
  isTosetDecidable→Discrete = isPosetDecidable→Discrete ∘ isToset→isPoset

  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isToset→isLosetIrreflKernel : IsToset R → isDecidable R → IsLoset (IrreflKernel R)
  isToset→isLosetIrreflKernel toset dec
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
                                  (IsToset.is-total toset b c))
                         (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → Rab , ¬a≡b)
                                   (λ Rba → (IsToset.is-trans toset b a c Rba Rac)
                                   , λ b≡c → ¬a≡b (IsToset.is-antisym toset a b
                                       (subst (λ x → R a x) (sym b≡c) Rac) Rba)))
                                 (IsToset.is-total toset a b))
                         (disc a b))
               λ { a b (¬¬Rab , ¬¬Rba) → IsToset.is-antisym toset a b
                                         (decRec (λ Rab → Rab)
                                           (λ ¬Rab → ⊥.rec (∥₁.rec isProp⊥
                                             (⊎.rec ¬Rab λ Rba → ¬¬Rba (Rba ,
                                               (λ b≡a → ¬Rab (subst (λ x → R x b) b≡a
                                                 (IsToset.is-refl toset b)))))
                                             (IsToset.is-total toset a b))) (dec a b))
                                         (decRec (λ Rba → Rba)
                                           (λ ¬Rba → ⊥.rec (∥₁.rec isProp⊥
                                             (⊎.rec ¬Rba λ Rab → ¬¬Rab (Rab ,
                                               (λ a≡b → ¬Rba (subst (λ x → R x a) a≡b
                                                 (IsToset.is-refl toset a)))))
                                             (IsToset.is-total toset b a))) (dec b a))}
    where disc : Discrete A
          disc = isTosetDecidable→Discrete toset dec

  isTosetDecidable→isLosetDecidable : IsToset R → isDecidable R → isDecidable (IrreflKernel R)
  isTosetDecidable→isLosetDecidable tos dec a b with dec a b
  ... | no ¬Rab = no λ { (Rab , _) → ¬Rab Rab }
  ... | yes Rab with (isTosetDecidable→Discrete tos dec) a b
  ...       | yes a≡b = no λ { (_ , ¬a≡b) → ¬a≡b a≡b }
  ...       | no  a≢b = yes (Rab , a≢b)

  isTosetInduced : IsToset R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsToset (InducedRelation R (B , f))
  isTosetInduced tos B (f , emb)
    = istoset (Embedding-into-isSet→isSet (f , emb) (IsToset.is-set tos))
              (λ a b → IsToset.is-prop-valued tos (f a) (f b))
              (λ a → IsToset.is-refl tos (f a))
              (λ a b c → IsToset.is-trans tos (f a) (f b) (f c))
              (λ a b a≤b b≤a → isEmbedding→Inj emb a b
                (IsToset.is-antisym tos (f a) (f b) a≤b b≤a))
              λ a b → IsToset.is-total tos (f a) (f b)

Toset→Poset : Toset ℓ ℓ' → Poset ℓ ℓ'
Toset→Poset (_ , tos) = _ , posetstr (TosetStr._≤_ tos)
                                     (isToset→isPoset (TosetStr.isToset tos))

Toset→Loset : (tos : Toset ℓ ℓ')
            → BinaryRelation.isDecidable (TosetStr._≤_ (snd tos))
            → Loset ℓ (ℓ-max ℓ ℓ')
Toset→Loset (_ , tos) dec
  = _ , losetstr (BinaryRelation.IrreflKernel (TosetStr._≤_ tos))
                 (isToset→isLosetIrreflKernel (TosetStr.isToset tos) dec)

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (tos : IsToset _≤_)
  where

  private
      pos = isToset→isPoset tos
      
      pre = isPoset→isProset pos  

      prop = IsToset.is-prop-valued tos

      rfl = IsToset.is-refl tos

      anti = IsToset.is-antisym tos

      trans = IsToset.is-trans tos

      total = IsToset.is-total tos

  module _
    {P : Embedding A ℓ''}
    where
    
    private
      toA = fst (snd P)

    isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
    isMinimal→isLeast n ism m
      = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (total (toA n) (toA m))

    isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
    isMaximal→isGreatest n ism m
      = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (total (toA n) (toA m))
