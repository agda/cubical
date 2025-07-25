module Cubical.Relation.Binary.Order.Apartness.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness.Base

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

open BinaryRelation

isApartness→ImpliesInequality : {A : Type ℓ} {_#_ : Rel A A ℓ'}
                              → IsApartness _#_ → ∀ x y → x # y → ¬ (x ≡ y)
isApartness→ImpliesInequality {_#_ = _#_} apart x y x#y x≡y
  = IsApartness.is-irrefl apart y (subst (λ a → a # y) x≡y x#y)

isApartness→isEquivRelNegationRel : {A : Type ℓ} {_#_ : Rel A A ℓ'}
                                  → IsApartness _#_ → isEquivRel (NegationRel _#_)
isApartness→isEquivRelNegationRel apart
  = equivRel (λ a a#a → IsApartness.is-irrefl apart a a#a)
                        (λ a b ¬a#b b#a → ¬a#b (IsApartness.is-sym apart b a b#a))
                         λ a b c ¬a#b ¬b#c a#c
                           → ∥₁.rec isProp⊥ (⊎.rec ¬a#b
                                    (λ c#b → ¬b#c (IsApartness.is-sym apart c b c#b)))
                                    (IsApartness.is-cotrans apart a c b a#c)

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isApartnessInduced : IsApartness R → (B : Type ℓ'') → (f : B ↪ A)
                     → IsApartness (InducedRelation R (B , f))
  isApartnessInduced apa B (f , emb)
    = isapartness (Embedding-into-isSet→isSet (f , emb) (IsApartness.is-set apa))
                  (λ a b → IsApartness.is-prop-valued apa (f a) (f b))
                  (λ a → IsApartness.is-irrefl apa (f a))
                  (λ a b c → IsApartness.is-cotrans apa (f a) (f b) (f c))
                  λ a b → IsApartness.is-sym apa (f a) (f b)

  isApartnessDual : IsApartness R → IsApartness (Dual R)
  isApartnessDual apa
    = isapartness (IsApartness.is-set apa)
                  (λ a b → IsApartness.is-prop-valued apa b a)
                  (IsApartness.is-irrefl apa)
                  (λ a b c Rba → ∥₁.map (⊎.rec (inl ∘ s c a)
                                               (inr ∘ s c b))
                                        (IsApartness.is-cotrans apa a b c (s a b Rba)))
                   s
    where s : isSym (Dual R)
          s a b = IsApartness.is-sym apa b a

DualApartness : Apartness ℓ ℓ' → Apartness ℓ ℓ'
DualApartness (_ , apa)
  = apartness _ (BinaryRelation.Dual (ApartnessStr._#_ apa))
                (isApartnessDual (ApartnessStr.isApartness apa))
