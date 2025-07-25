module Cubical.Relation.Binary.Order.Quoset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  private
    transrefl : isTrans R → isTrans (ReflClosure R)
    transrefl trans a b c (inl Rab) (inl Rbc) = inl (trans a b c Rab Rbc)
    transrefl trans a b c (inl Rab) (inr b≡c) = inl (subst (R a) b≡c Rab)
    transrefl trans a b c (inr a≡b) (inl Rbc) = inl (subst (λ z → R z c) (sym a≡b) Rbc)
    transrefl trans a b c (inr a≡b) (inr b≡c) = inr (a≡b ∙ b≡c)

    antisym : isIrrefl R → isTrans R → isAntisym (ReflClosure R)
    antisym irr trans a b (inl Rab) (inl Rba) = ⊥.rec (irr a (trans a b a Rab Rba))
    antisym irr trans a b (inl _) (inr b≡a) = sym b≡a
    antisym irr trans a b (inr a≡b) _ = a≡b

  isQuoset→isPosetReflClosure : IsQuoset R → IsPoset (ReflClosure R)
  isQuoset→isPosetReflClosure quoset
    = isposet (IsQuoset.is-set quoset)
              (λ a b → isProp⊎ (IsQuoset.is-prop-valued quoset a b)
                               (IsQuoset.is-set quoset a b)
                                 λ Rab a≡b
                                   → IsQuoset.is-irrefl quoset a (subst (R a)
                                                                           (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsQuoset.is-trans quoset))
              (antisym (IsQuoset.is-irrefl quoset)
                       (IsQuoset.is-trans quoset))

  isQuosetInduced : IsQuoset R → (B : Type ℓ'') → (f : B ↪ A)
                       → IsQuoset (InducedRelation R (B , f))
  isQuosetInduced quo B (f , emb)
    = isquoset (Embedding-into-isSet→isSet (f , emb)
                                                (IsQuoset.is-set quo))
                    (λ a b → IsQuoset.is-prop-valued quo (f a) (f b))
                    (λ a → IsQuoset.is-irrefl quo (f a))
                    (λ a b c → IsQuoset.is-trans quo (f a) (f b) (f c))
                    λ a b → IsQuoset.is-asym quo (f a) (f b)

  isQuosetDual : IsQuoset R → IsQuoset (Dual R)
  isQuosetDual quo
    = isquoset (IsQuoset.is-set quo)
               (λ a b → IsQuoset.is-prop-valued quo b a)
               (IsQuoset.is-irrefl quo)
               (λ a b c Rab Rbc → IsQuoset.is-trans quo c b a Rbc Rab)
                λ a b → IsQuoset.is-asym quo b a

Quoset→Poset : Quoset ℓ ℓ' → Poset ℓ (ℓ-max ℓ ℓ')
Quoset→Poset (_ , quo)
  = poset _ (BinaryRelation.ReflClosure (QuosetStr._<_ quo))
            (isQuoset→isPosetReflClosure (QuosetStr.isQuoset quo))

DualQuoset : Quoset ℓ ℓ' → Quoset ℓ ℓ'
DualQuoset (_ , quo)
  = quoset _ (BinaryRelation.Dual (QuosetStr._<_ quo))
             (isQuosetDual (QuosetStr.isQuoset quo))
