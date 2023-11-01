{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.StrictPoset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.StrictPoset.Base

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

  isStrictPoset→isPosetReflClosure : IsStrictPoset R → IsPoset (ReflClosure R)
  isStrictPoset→isPosetReflClosure strictposet
    = isposet (IsStrictPoset.is-set strictposet)
              (λ a b → isProp⊎ (IsStrictPoset.is-prop-valued strictposet a b)
                               (IsStrictPoset.is-set strictposet a b)
                                 λ Rab a≡b
                                   → IsStrictPoset.is-irrefl strictposet a (subst (R a)
                                                                           (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsStrictPoset.is-trans strictposet))
              (antisym (IsStrictPoset.is-irrefl strictposet)
                       (IsStrictPoset.is-trans strictposet))

  isStrictPoset→isApartnessSymClosure : IsStrictPoset R
                                      → isWeaklyLinear R
                                      → IsApartness (SymClosure R)
  isStrictPoset→isApartnessSymClosure strictposet weak
    = isapartness (IsStrictPoset.is-set strictposet)
                  (λ a b → isProp⊎ (IsStrictPoset.is-prop-valued strictposet a b)
                                   (IsStrictPoset.is-prop-valued strictposet b a)
                                   (IsStrictPoset.is-asym strictposet a b))
                  (λ a x → ⊎.rec (IsStrictPoset.is-irrefl strictposet a)
                                 (IsStrictPoset.is-irrefl strictposet a) x)
                  (λ a b c x → ⊎.rec (λ Rab → ∥₁.map (⊎.map (λ Rac → inl Rac)
                                                             (λ Rcb → inr Rcb))
                                                      (weak a b c Rab))
                                     (λ Rba → ∥₁.rec isPropPropTrunc
                                                     (λ y → ∣ ⊎.rec (λ Rbc → inr (inl Rbc))
                                                     (λ Rca → inl (inr Rca)) y ∣₁)
                                                     (weak b a c Rba)) x)
                  (isSymSymClosure R)

  isStrictPosetInduced : IsStrictPoset R → (B : Type ℓ'') → (f : B ↪ A)
                       → IsStrictPoset (InducedRelation R (B , f))
  isStrictPosetInduced strictpos B (f , emb)
    = isstrictposet (Embedding-into-isSet→isSet (f , emb)
                                                (IsStrictPoset.is-set strictpos))
                    (λ a b → IsStrictPoset.is-prop-valued strictpos (f a) (f b))
                    (λ a → IsStrictPoset.is-irrefl strictpos (f a))
                    (λ a b c → IsStrictPoset.is-trans strictpos (f a) (f b) (f c))
                    λ a b → IsStrictPoset.is-asym strictpos (f a) (f b)

StrictPoset→Poset : StrictPoset ℓ ℓ' → Poset ℓ (ℓ-max ℓ ℓ')
StrictPoset→Poset (_ , strictpos)
  = _ , posetstr (BinaryRelation.ReflClosure (StrictPosetStr._<_ strictpos))
                 (isStrictPoset→isPosetReflClosure (StrictPosetStr.isStrictPoset strictpos))

StrictPoset→Apartness : (R : StrictPoset ℓ ℓ')
                      → BinaryRelation.isWeaklyLinear (StrictPosetStr._<_ (snd R))
                      → Apartness ℓ ℓ'
StrictPoset→Apartness (_ , strictpos) weak
  = _ , apartnessstr (BinaryRelation.SymClosure (StrictPosetStr._<_ strictpos))
                     (isStrictPoset→isApartnessSymClosure
                       (StrictPosetStr.isStrictPoset strictpos) weak)
