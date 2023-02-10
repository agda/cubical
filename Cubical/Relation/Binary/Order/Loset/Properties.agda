{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Loset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Toset.Base
open import Cubical.Relation.Binary.Order.StrictPoset.Base
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

  isLoset→isStrictPoset : IsLoset R → IsStrictPoset R
  isLoset→isStrictPoset loset = isstrictposet
                                (IsLoset.is-set loset)
                                (IsLoset.is-prop-valued loset)
                                (IsLoset.is-irrefl loset)
                                (IsLoset.is-trans loset)
                                (IsLoset.is-asym loset)

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

  isLoset→isTosetReflClosure : Discrete A → IsLoset R → IsToset (ReflClosure R)
  isLoset→isTosetReflClosure disc loset
    = istoset (IsLoset.is-set loset)
              (λ a b → isProp⊎ (IsLoset.is-prop-valued loset a b)
                               (IsLoset.is-set loset a b)
                               λ Rab a≡b
                                 → IsLoset.is-irrefl loset a (subst (R a)
                                                             (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsLoset.is-trans loset))
              (antisym (IsLoset.is-irrefl loset)
                       (IsLoset.is-trans loset))
              λ a b → decRec (λ a≡b → ∣ inl (inr a≡b) ∣₁)
                             (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → inl Rab) λ Rba → inl Rba)
                             (IsLoset.is-connected loset a b ¬a≡b)) (disc a b)

  isLosetInduced : IsLoset R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsLoset (InducedRelation R (B , f))
  isLosetInduced los B (f , emb)
    = isloset (Embedding-into-isSet→isSet (f , emb) (IsLoset.is-set los))
              (λ a b → IsLoset.is-prop-valued los (f a) (f b))
              (λ a → IsLoset.is-irrefl los (f a))
              (λ a b c → IsLoset.is-trans los (f a) (f b) (f c))
              (λ a b → IsLoset.is-asym los (f a) (f b))
              (λ a b c → IsLoset.is-weakly-linear los (f a) (f b) (f c))
              λ a b ¬a≡b → IsLoset.is-connected los (f a) (f b)
                λ fa≡fb → ¬a≡b (isEmbedding→Inj emb a b fa≡fb)

Loset→StrictPoset : Loset ℓ ℓ' → StrictPoset ℓ ℓ'
Loset→StrictPoset (_ , los)
  = _ , strictposetstr (LosetStr._<_ los)
                       (isLoset→isStrictPoset (LosetStr.isLoset los))

Loset→Toset : (los : Loset ℓ ℓ')
            → Discrete (fst los)
            → Toset ℓ (ℓ-max ℓ ℓ')
Loset→Toset (_ , los) disc
  = _ , tosetstr (BinaryRelation.ReflClosure (LosetStr._<_ los))
                 (isLoset→isTosetReflClosure disc
                                             (LosetStr.isLoset los))
