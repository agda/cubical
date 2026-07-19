module Cubical.Relation.Binary.Order.Loset.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base
open import Cubical.Relation.Binary.Order.Toset
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.StrictOrder.Base
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

  isLoset→isStrictOrder : IsLoset R → IsStrictOrder R
  isLoset→isStrictOrder loset = isstrictorder
                          (IsLoset.is-set loset)
                          (IsLoset.is-prop-valued loset)
                          (IsLoset.is-irrefl loset)
                          (IsLoset.is-trans loset)
                          (IsLoset.is-asym loset)
                          (IsLoset.is-weakly-linear loset)

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

  isLoset→isTosetReflClosure : IsLoset R → isDecidable R → IsToset (ReflClosure R)
  isLoset→isTosetReflClosure loset dec
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
               λ a b → decRec (λ Rab → ∣ inl (inl Rab) ∣₁)
                              (λ ¬Rab → decRec (λ Rba → ∣ inr (inl Rba) ∣₁)
                                               (λ ¬Rba → ∣ inl (inr (IsLoset.is-connected loset a b
                                                                    (¬Rab , ¬Rba))) ∣₁)
                                        (dec b a))
                       (dec a b)

  isLosetDecidable→isTosetDecidable : IsLoset R → isDecidable R → isDecidable (ReflClosure R)
  isLosetDecidable→isTosetDecidable los dec a b with dec a b
  ... | yes Rab = yes (inl Rab)
  ... | no ¬Rab with dec b a
  ...       | yes Rba = no (⊎.rec ¬Rab λ a≡b → IsLoset.is-irrefl los b (subst (R b) a≡b Rba))
  ...       | no ¬Rba = yes (inr (IsLoset.is-connected los a b (¬Rab , ¬Rba)))

  isLosetDecidable→Discrete : IsLoset R → isDecidable R → Discrete A
  isLosetDecidable→Discrete los dec = isTosetDecidable→Discrete
                                     (isLoset→isTosetReflClosure los dec)
                                     (isLosetDecidable→isTosetDecidable los dec)

  isLoset→isPosetNegationRel : IsLoset R → IsPoset (NegationRel R)
  isLoset→isPosetNegationRel loset
    = isposet (IsLoset.is-set loset)
              (λ a b → isProp¬ (R a b))
              (IsLoset.is-irrefl loset)
              (λ a b c ¬Rab ¬Rbc Rac → ∥₁.rec isProp⊥ (⊎.rec ¬Rab ¬Rbc)
                                             (IsLoset.is-weakly-linear loset a c b Rac))
               λ a b ¬Rab ¬Rba → IsLoset.is-connected loset a b (¬Rab , ¬Rba)

  isLosetInduced : IsLoset R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsLoset (InducedRelation R (B , f))
  isLosetInduced los B (f , emb)
    = isloset (Embedding-into-isSet→isSet (f , emb) (IsLoset.is-set los))
              (λ a b → IsLoset.is-prop-valued los (f a) (f b))
              (λ a → IsLoset.is-irrefl los (f a))
              (λ a b c → IsLoset.is-trans los (f a) (f b) (f c))
              (λ a b → IsLoset.is-asym los (f a) (f b))
              (λ a b c → IsLoset.is-weakly-linear los (f a) (f b) (f c))
               λ a b ineq → isEmbedding→Inj emb a b
                           (IsLoset.is-connected los (f a) (f b) ineq)

  isLosetDual : IsLoset R → IsLoset (Dual R)
  isLosetDual los
    = isloset (IsLoset.is-set los)
              (λ a b → IsLoset.is-prop-valued los b a)
              (IsLoset.is-irrefl los)
              (λ a b c Rab Rbc → IsLoset.is-trans los c b a Rbc Rab)
              (λ a b → IsLoset.is-asym los b a)
              (λ a b c Rba → ∥₁.map (⊎.rec inr inl)
                                    (IsLoset.is-weakly-linear los b a c Rba))
               λ { a b (¬Rba , ¬Rab) → IsLoset.is-connected los a b (¬Rab , ¬Rba) }

Loset→StrictOrder : Loset ℓ ℓ' → StrictOrder ℓ ℓ'
Loset→StrictOrder (_ , los)
  = strictorder _ (LosetStr._<_ los)
                  (isLoset→isStrictOrder (LosetStr.isLoset los))

Loset→Toset : (los : Loset ℓ ℓ')
            → BinaryRelation.isDecidable (LosetStr._<_ (snd los))
            → Toset ℓ (ℓ-max ℓ ℓ')
Loset→Toset (_ , los) dec
  = toset _ (BinaryRelation.ReflClosure (LosetStr._<_ los))
            (isLoset→isTosetReflClosure (LosetStr.isLoset los) dec)

DualLoset : Loset ℓ ℓ' → Loset ℓ ℓ'
DualLoset (_ , los)
  = loset _ (BinaryRelation.Dual (LosetStr._<_ los))
            (isLosetDual (LosetStr.isLoset los))
