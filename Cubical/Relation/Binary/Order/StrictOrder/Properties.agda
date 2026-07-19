module Cubical.Relation.Binary.Order.StrictOrder.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Toset
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Proset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base
open import Cubical.Relation.Binary.Order.StrictOrder.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isStrictOrder→isQuoset : IsStrictOrder R → IsQuoset R
  isStrictOrder→isQuoset strictorder = isquoset
                        (IsStrictOrder.is-set strictorder)
                        (IsStrictOrder.is-prop-valued strictorder)
                        (IsStrictOrder.is-irrefl strictorder)
                        (IsStrictOrder.is-trans strictorder)
                        (IsStrictOrder.is-asym strictorder)

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

  isStrictOrder→isApartnessSymClosure : IsStrictOrder R
                                      → IsApartness (SymClosure R)
  isStrictOrder→isApartnessSymClosure strict
    = isapartness (IsStrictOrder.is-set strict)
                  (λ a b → isProp⊎ (IsStrictOrder.is-prop-valued strict a b)
                                   (IsStrictOrder.is-prop-valued strict b a)
                                   (IsStrictOrder.is-asym strict a b))
                  (λ a x → ⊎.rec (IsStrictOrder.is-irrefl strict a)
                                 (IsStrictOrder.is-irrefl strict a) x)
                  (λ a b c x → ⊎.rec (λ Rab → ∥₁.map (⊎.map (λ Rac → inl Rac)
                                                             (λ Rcb → inr Rcb))
                                                      (IsStrictOrder.is-weakly-linear strict a b c Rab))
                                     (λ Rba → ∥₁.rec isPropPropTrunc
                                                     (λ y → ∣ ⊎.rec (λ Rbc → inr (inl Rbc))
                                                     (λ Rca → inl (inr Rca)) y ∣₁)
                                                     (IsStrictOrder.is-weakly-linear strict b a c Rba)) x)
                  (isSymSymClosure R)

  isStrictOrder→isProsetNegationRel : IsStrictOrder R
                                    → IsProset (NegationRel R)
  isStrictOrder→isProsetNegationRel strict
    = isproset (IsStrictOrder.is-set strict)
               (λ _ _ → isProp¬ _)
               (IsStrictOrder.is-irrefl strict)
                λ a b c ¬Rab ¬Rbc Rac →
                    ∥₁.rec isProp⊥ (⊎.rec ¬Rab ¬Rbc)
                          (IsStrictOrder.is-weakly-linear strict a c b Rac)

  isStrictOrderInduced : IsStrictOrder R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsStrictOrder (InducedRelation R (B , f))
  isStrictOrderInduced strict B (f , emb)
    = isstrictorder (Embedding-into-isSet→isSet (f , emb) (IsStrictOrder.is-set strict))
              (λ a b → IsStrictOrder.is-prop-valued strict (f a) (f b))
              (λ a → IsStrictOrder.is-irrefl strict (f a))
              (λ a b c → IsStrictOrder.is-trans strict (f a) (f b) (f c))
              (λ a b → IsStrictOrder.is-asym strict (f a) (f b))
               λ a b c → IsStrictOrder.is-weakly-linear strict (f a) (f b) (f c)

  isStrictOrderDual : IsStrictOrder R → IsStrictOrder (Dual R)
  isStrictOrderDual strict
    = isstrictorder (IsStrictOrder.is-set strict)
                    (λ a b → IsStrictOrder.is-prop-valued strict b a)
                    (IsStrictOrder.is-irrefl strict)
                    (λ a b c Rab Rbc → IsStrictOrder.is-trans strict c b a Rbc Rab)
                    (λ a b → IsStrictOrder.is-asym strict b a)
                    (λ a b c Rba → ∥₁.map (⊎.rec inr inl)
                                          (IsStrictOrder.is-weakly-linear strict b a c Rba))

StrictOrder→Quoset : StrictOrder ℓ ℓ' → Quoset ℓ ℓ'
StrictOrder→Quoset (_ , strict)
  = quoset _ (StrictOrderStr._<_ strict)
             (isStrictOrder→isQuoset (StrictOrderStr.isStrictOrder strict))

StrictOrder→Apartness : StrictOrder ℓ ℓ' → Apartness ℓ ℓ'
StrictOrder→Apartness (_ , strict)
  = apartness _ (BinaryRelation.SymClosure (StrictOrderStr._<_ strict))
                (isStrictOrder→isApartnessSymClosure (StrictOrderStr.isStrictOrder strict))

StrictOrder→Proset : StrictOrder ℓ ℓ' → Proset ℓ ℓ'
StrictOrder→Proset (_ , strict)
  = proset _ (BinaryRelation.NegationRel (StrictOrderStr._<_ strict))
             (isStrictOrder→isProsetNegationRel (StrictOrderStr.isStrictOrder strict))

DualStrictOrder : StrictOrder ℓ ℓ' → StrictOrder ℓ ℓ'
DualStrictOrder (_ , strict)
  = strictorder _ (BinaryRelation.Dual (StrictOrderStr._<_ strict))
                  (isStrictOrderDual (StrictOrderStr.isStrictOrder strict))
