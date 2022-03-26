{-

Properties and Formulae about Cardinality

This file contains:
- Relation between abstract properties and cardinality in special cases;
- Combinatorial formulae, namely, cardinality of A+B, A×B, ΣAB, ΠAB, etc;
- A general form of Pigeonhole Principle;
- Maximal value of numerical function on finite sets;
- Set truncation of FinSet is equivalent to ℕ;
- FinProp is equivalent to Bool.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Cardinality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetTruncation as Set

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.Fin using (Fin-inj)
open import Cubical.Data.Fin.LehmerCode as LehmerCode
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.FiniteChoice
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Induction hiding (_+_)

open import Cubical.Relation.Nullary

open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' ℓ'' : Level
    n : ℕ
    X : FinSet ℓ
    Y : FinSet ℓ'

-- cardinality of finite sets

∣≃card∣ : (X : FinSet ℓ) → ∥ X .fst ≃ Fin (card X) ∥
∣≃card∣ X = X .snd .snd

-- cardinality is invariant under equivalences

cardEquiv : (X : FinSet ℓ)(Y : FinSet ℓ') → ∥ X .fst ≃ Y .fst ∥ → card X ≡ card Y
cardEquiv X Y e =
  Prop.rec (isSetℕ _ _) (λ p → Fin-inj _ _ (ua p))
    (∣ invEquiv (SumFin≃Fin _) ∣ ⋆̂ ∣invEquiv∣ (∣≃card∣ X) ⋆̂ e ⋆̂ ∣≃card∣ Y ⋆̂ ∣ SumFin≃Fin _ ∣)

cardInj : card X ≡ card Y → ∥ X .fst ≃ Y .fst ∥
cardInj {X = X} {Y = Y} p =
  ∣≃card∣ X ⋆̂ ∣ pathToEquiv (cong Fin p) ∣ ⋆̂ ∣invEquiv∣ (∣≃card∣ Y)

cardReflection : card X ≡ n → ∥ X .fst ≃ Fin n ∥
cardReflection {X = X} = cardInj {X = X} {Y = _ , isFinSetFin}

card≡MereEquiv : (card X ≡ card Y) ≡ ∥ X .fst ≃ Y .fst ∥
card≡MereEquiv {X = X} {Y = Y} =
  hPropExt (isSetℕ _ _) isPropPropTrunc (cardInj {X = X} {Y = Y}) (cardEquiv X Y)

-- special properties about specific cardinality

module _
  {X : FinSet ℓ} where

  card≡0→isEmpty : card X ≡ 0 → ¬ X .fst
  card≡0→isEmpty p x =
    Prop.rec isProp⊥ (λ e → subst Fin p (e .fst x)) (∣≃card∣ X)

  card>0→isInhab : card X > 0 → ∥ X .fst ∥
  card>0→isInhab p =
    Prop.map (λ e → invEq e (Fin>0→isInhab _ p)) (∣≃card∣ X)

  card>1→hasNonEqualTerm : card X > 1 → ∥ Σ[ a ∈ X .fst ] Σ[ b ∈ X .fst ] ¬ a ≡ b ∥
  card>1→hasNonEqualTerm p =
    Prop.map
      (λ e →
        e .fst (Fin>1→hasNonEqualTerm _ p .fst) ,
        e .fst (Fin>1→hasNonEqualTerm _ p .snd .fst) ,
        Fin>1→hasNonEqualTerm _ p .snd .snd ∘ invEq (congEquiv e))
      (∣invEquiv∣ (∣≃card∣ X))

  card≡1→isContr : card X ≡ 1 → isContr (X .fst)
  card≡1→isContr p =
    Prop.rec isPropIsContr
        (λ e → isOfHLevelRespectEquiv 0 (invEquiv (e ⋆ substEquiv Fin p)) isContrSumFin1) (∣≃card∣ X)

  card≤1→isProp : card X ≤ 1 → isProp (X .fst)
  card≤1→isProp p =
    Prop.rec isPropIsProp (λ e → isOfHLevelRespectEquiv 1 (invEquiv e) (Fin≤1→isProp (card X) p)) (∣≃card∣ X)

  card≡n : card X ≡ n → ∥ X ≡ 𝔽in n ∥
  card≡n {n = n} p =
    Prop.map
        (λ e →
          (λ i →
            ua e i ,
            isProp→PathP {B = λ j → isFinSet (ua e j)}
              (λ _ → isPropIsFinSet) (X .snd) (𝔽in n .snd) i ))
        (∣≃card∣ X ⋆̂ ∣ pathToEquiv (cong Fin p) ⋆ invEquiv (𝔽in≃Fin n) ∣)

  card≡0 : card X ≡ 0 → X ≡ 𝟘
  card≡0 p =
    propTruncIdempotent≃
      (isOfHLevelRespectEquiv
        1 (FinSet≡ X 𝟘)
          (isOfHLevel≡ 1
            (card≤1→isProp (subst (λ a → a ≤ 1) (sym p) (≤-solver 0 1))) (isProp⊥*))) .fst
      (card≡n p)

  card≡1 : card X ≡ 1 → X ≡ 𝟙
  card≡1 p =
    propTruncIdempotent≃
      (isOfHLevelRespectEquiv
        1 (FinSet≡ X 𝟙)
          (isOfHLevel≡ 1
            (card≤1→isProp (subst (λ a → a ≤ 1) (sym p) (≤-solver 1 1))) (isPropUnit*))) .fst
      (Prop.map (λ q → q ∙ 𝔽in1≡𝟙) (card≡n p))

module _
  (X : FinSet ℓ) where

  isEmpty→card≡0 : ¬ X .fst → card X ≡ 0
  isEmpty→card≡0 p =
    Prop.rec (isSetℕ _ _) (λ e → sym (isEmpty→Fin≡0 _ (p ∘ invEq e))) (∣≃card∣ X)

  isInhab→card>0 : ∥ X .fst ∥ → card X > 0
  isInhab→card>0 = Prop.rec2 m≤n-isProp (λ p x → isInhab→Fin>0 _ (p .fst x)) (∣≃card∣ X)

  hasNonEqualTerm→card>1 : {a b : X. fst} → ¬ a ≡ b → card X > 1
  hasNonEqualTerm→card>1 {a = a} {b = b} q =
    Prop.rec m≤n-isProp (λ p → hasNonEqualTerm→Fin>1 _ (p .fst a) (p .fst b) (q ∘ invEq (congEquiv p))) (∣≃card∣ X)

  isContr→card≡1 : isContr (X .fst) → card X ≡ 1
  isContr→card≡1 p = cardEquiv X (_ , isFinSetUnit) ∣ isContr→≃Unit p ∣

  isProp→card≤1 : isProp (X .fst) → card X ≤ 1
  isProp→card≤1 p = isProp→Fin≤1 (card X) (Prop.rec isPropIsProp (λ e → isOfHLevelRespectEquiv 1 e p) (∣≃card∣ X))

{- formulae about cardinality -}

-- results to be used in direct induction on FinSet

card𝟘 : card (𝟘 {ℓ}) ≡ 0
card𝟘 {ℓ = ℓ} = isEmpty→card≡0 (𝟘 {ℓ}) (Empty.rec*)

card𝟙 : card (𝟙 {ℓ}) ≡ 1
card𝟙 {ℓ = ℓ} = isContr→card≡1 (𝟙 {ℓ}) isContrUnit*

card𝔽in : (n : ℕ) → card (𝔽in {ℓ} n) ≡ n
card𝔽in {ℓ = ℓ} n =  cardEquiv (𝔽in {ℓ} n) (_ , isFinSetFin) ∣ 𝔽in≃Fin n ∣

-- addition/product formula

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  card+ : card (_ , isFinSet⊎ X Y) ≡ card X + card Y
  card+ = refl

  card× : card (_ , isFinSet× X Y) ≡ card X · card Y
  card× = refl

-- total summation/product of numerical functions from finite sets

module _
  (X : FinSet ℓ)
  (f : X .fst → ℕ) where

  sum : ℕ
  sum = card (_ , isFinSetΣ X (λ x → Fin (f x) , isFinSetFin))

  prod : ℕ
  prod = card (_ , isFinSetΠ X (λ x → Fin (f x) , isFinSetFin))

module _
  (f : 𝟘 {ℓ} .fst → ℕ) where

  sum𝟘 : sum 𝟘 f ≡ 0
  sum𝟘 =
    isEmpty→card≡0 (_ , isFinSetΣ 𝟘 (λ x → Fin (f x) , isFinSetFin))
                   ((invEquiv (Σ-cong-equiv-fst (invEquiv 𝟘≃Empty)) ⋆ ΣEmpty _) .fst)

  prod𝟘 : prod 𝟘 f ≡ 1
  prod𝟘 =
    isContr→card≡1 (_ , isFinSetΠ 𝟘 (λ x → Fin (f x) , isFinSetFin))
                   (isContrΠ⊥*)

module _
  (f : 𝟙 {ℓ} .fst → ℕ) where

  sum𝟙 : sum 𝟙 f ≡ f tt*
  sum𝟙 =
    cardEquiv (_ , isFinSetΣ 𝟙 (λ x → Fin (f x) , isFinSetFin))
              (Fin (f tt*) , isFinSetFin) ∣ Σ-contractFst isContrUnit* ∣

  prod𝟙 : prod 𝟙 f ≡ f tt*
  prod𝟙 =
    cardEquiv (_ , isFinSetΠ 𝟙 (λ x → Fin (f x) , isFinSetFin))
              (Fin (f tt*) , isFinSetFin) ∣ ΠUnit* _ ∣

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ')
  (f : X .fst ⊎ Y .fst → ℕ) where

  sum⊎ : sum (_ , isFinSet⊎ X Y) f ≡ sum X (f ∘ inl) + sum Y (f ∘ inr)
  sum⊎ =
    cardEquiv (_ , isFinSetΣ (_ , isFinSet⊎ X Y) (λ x → Fin (f x) , isFinSetFin))
              (_ , isFinSet⊎ (_ , isFinSetΣ X (λ x → Fin (f (inl x)) , isFinSetFin))
                             (_ , isFinSetΣ Y (λ y → Fin (f (inr y)) , isFinSetFin))) ∣ Σ⊎≃ ∣
    ∙ card+ (_ , isFinSetΣ X (λ x → Fin (f (inl x)) , isFinSetFin))
            (_ , isFinSetΣ Y (λ y → Fin (f (inr y)) , isFinSetFin))

  prod⊎ : prod (_ , isFinSet⊎ X Y) f ≡ prod X (f ∘ inl) · prod Y (f ∘ inr)
  prod⊎ =
    cardEquiv (_ , isFinSetΠ (_ , isFinSet⊎ X Y) (λ x → Fin (f x) , isFinSetFin))
              (_ , isFinSet× (_ , isFinSetΠ X (λ x → Fin (f (inl x)) , isFinSetFin))
                             (_ , isFinSetΠ Y (λ y → Fin (f (inr y)) , isFinSetFin))) ∣ Π⊎≃ ∣
    ∙ card× (_ , isFinSetΠ X (λ x → Fin (f (inl x)) , isFinSetFin))
            (_ , isFinSetΠ Y (λ y → Fin (f (inr y)) , isFinSetFin))

-- technical lemma
module _
  (n : ℕ)(f : 𝔽in {ℓ} (1 + n) .fst → ℕ) where

  sum𝔽in1+n : sum (𝔽in (1 + n)) f ≡ f (inl tt*) + sum (𝔽in n) (f ∘ inr)
  sum𝔽in1+n = sum⊎ 𝟙 (𝔽in n) f ∙ (λ i → sum𝟙 (f ∘ inl) i + sum (𝔽in n) (f ∘ inr))

  prod𝔽in1+n : prod (𝔽in (1 + n)) f ≡ f (inl tt*) · prod (𝔽in n) (f ∘ inr)
  prod𝔽in1+n = prod⊎ 𝟙 (𝔽in n) f ∙ (λ i → prod𝟙 (f ∘ inl) i · prod (𝔽in n) (f ∘ inr))

sumConst𝔽in : (n : ℕ)(f : 𝔽in {ℓ} n .fst → ℕ)(c : ℕ)(h : (x : 𝔽in n .fst) → f x ≡ c) → sum (𝔽in n) f ≡ c · n
sumConst𝔽in 0 f c _ = sum𝟘 f ∙ 0≡m·0 c
sumConst𝔽in (suc n) f c h =
    sum𝔽in1+n n f
  ∙ (λ i → h (inl tt*) i + sumConst𝔽in n (f ∘ inr) c (h ∘ inr) i)
  ∙ sym (·-suc c n)

prodConst𝔽in : (n : ℕ)(f : 𝔽in {ℓ} n .fst → ℕ)(c : ℕ)(h : (x : 𝔽in n .fst) → f x ≡ c) → prod (𝔽in n) f ≡ c ^ n
prodConst𝔽in 0 f c _ = prod𝟘 f
prodConst𝔽in (suc n) f c h =
    prod𝔽in1+n n f
  ∙ (λ i → h (inl tt*) i · prodConst𝔽in n (f ∘ inr) c (h ∘ inr) i)

module _
  (X : FinSet ℓ)
  (f : X .fst → ℕ)
  (c : ℕ)(h : (x : X .fst) → f x ≡ c) where

  sumConst : sum X f ≡ c · card X
  sumConst =
    elimProp
      (λ X → (f : X .fst → ℕ)(c : ℕ)(h : (x : X .fst) → f x ≡ c) → sum X f ≡ c · (card X))
      (λ X → isPropΠ3 (λ _ _ _ → isSetℕ _ _))
      (λ n f c h → sumConst𝔽in n f c h ∙ (λ i → c · card𝔽in {ℓ = ℓ} n (~ i))) X f c h

  prodConst : prod X f ≡ c ^ card X
  prodConst =
    elimProp
      (λ X → (f : X .fst → ℕ)(c : ℕ)(h : (x : X .fst) → f x ≡ c) → prod X f ≡ c ^ (card X))
      (λ X → isPropΠ3 (λ _ _ _ → isSetℕ _ _))
      (λ n f c h → prodConst𝔽in n f c h ∙ (λ i → c ^ card𝔽in {ℓ = ℓ} n (~ i))) X f c h

private
  ≡≤ : {m n l k r s : ℕ} → m ≤ n → l ≤ k → r ≡ m + l → s ≡ n + k → r ≤ s
  ≡≤ {m = m} {l = l} {k = k} p q u v = subst2 (_≤_) (sym u) (sym v) (≤-+-≤ p q)

  ≡< : {m n l k r s : ℕ} → m < n → l ≤ k → r ≡ m + l → s ≡ n + k → r < s
  ≡< {m = m} {l = l} {k = k} p q u v = subst2 (_<_) (sym u) (sym v) (<-+-≤ p q)

sum≤𝔽in : (n : ℕ)(f g : 𝔽in {ℓ} n .fst → ℕ)(h : (x : 𝔽in n .fst) → f x ≤ g x) → sum (𝔽in n) f ≤ sum (𝔽in n) g
sum≤𝔽in 0 f g _ = subst2 (_≤_) (sym (sum𝟘 f)) (sym (sum𝟘 g)) ≤-refl
sum≤𝔽in (suc n) f g h =
  ≡≤ (h (inl tt*)) (sum≤𝔽in n (f ∘ inr) (g ∘ inr) (h ∘ inr)) (sum𝔽in1+n n f) (sum𝔽in1+n n g)

sum<𝔽in : (n : ℕ)(f g : 𝔽in {ℓ} n .fst → ℕ)(t : ∥ 𝔽in {ℓ} n .fst ∥)(h : (x : 𝔽in n .fst) → f x < g x)
  → sum (𝔽in n) f < sum (𝔽in n) g
sum<𝔽in {ℓ = ℓ} 0 _ _ t _ = Empty.rec (<→≢ (isInhab→card>0 (𝔽in 0) t) (card𝟘 {ℓ = ℓ}))
sum<𝔽in (suc n) f g t h =
  ≡< (h (inl tt*)) (sum≤𝔽in n (f ∘ inr) (g ∘ inr) (<-weaken ∘ h ∘ inr)) (sum𝔽in1+n n f) (sum𝔽in1+n n g)

module _
  (X : FinSet ℓ)
  (f g : X .fst → ℕ) where

    module _
      (h : (x : X .fst) → f x ≡ g x) where

      sum≡ : sum X f ≡ sum X g
      sum≡ i = sum X (λ x → h x i)

      prod≡ : prod X f ≡ prod X g
      prod≡ i = prod X (λ x → h x i)

    module _
      (h : (x : X .fst) → f x ≤ g x) where

      sum≤ : sum X f ≤ sum X g
      sum≤ =
        elimProp
          (λ X → (f g : X .fst → ℕ)(h : (x : X .fst) → f x ≤ g x) → sum X f ≤ sum X g)
          (λ X → isPropΠ3 (λ _ _ _ → m≤n-isProp)) sum≤𝔽in X f g h

    module _
      (t : ∥ X .fst ∥)
      (h : (x : X .fst) → f x < g x) where

      sum< : sum X f < sum X g
      sum< =
        elimProp
          (λ X → (f g : X .fst → ℕ)(t : ∥ X .fst ∥)(h : (x : X .fst) → f x < g x) → sum X f < sum X g)
          (λ X → isPropΠ4 (λ _ _ _ _ → m≤n-isProp)) sum<𝔽in X f g t h

module _
  (X : FinSet ℓ)
  (f : X .fst → ℕ) where

  module _
    (c : ℕ)(h : (x : X .fst) → f x ≤ c) where

    sumBounded : sum X f ≤ c · card X
    sumBounded = subst (λ a → sum X f ≤ a) (sumConst X (λ _ → c) c (λ _ → refl)) (sum≤ X f (λ _ → c) h)

  module _
    (c : ℕ)(h : (x : X .fst) → f x ≥ c) where

    sumBoundedBelow : sum X f ≥ c · card X
    sumBoundedBelow = subst (λ a → sum X f ≥ a) (sumConst X (λ _ → c) c (λ _ → refl)) (sum≤ X (λ _ → c) f h)

-- some combinatorial identities

module _
  (X : FinSet ℓ )
  (Y : X .fst → FinSet ℓ') where

  cardΣ : card (_ , isFinSetΣ X Y) ≡ sum X (λ x → card (Y x))
  cardΣ =
    cardEquiv (_ , isFinSetΣ X Y) (_ , isFinSetΣ X (λ x → Fin (card (Y x)) , isFinSetFin))
              (Prop.map Σ-cong-equiv-snd
                (choice X (λ x → Y x .fst ≃ Fin (card (Y x))) (λ x → ∣≃card∣ (Y x))))

  cardΠ : card (_ , isFinSetΠ X Y) ≡ prod X (λ x → card (Y x))
  cardΠ =
    cardEquiv (_ , isFinSetΠ X Y) (_ , isFinSetΠ X (λ x → Fin (card (Y x)) , isFinSetFin))
              (Prop.map equivΠCod
                (choice X (λ x → Y x .fst ≃ Fin (card (Y x))) (λ x → ∣≃card∣ (Y x))))

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  card→ : card (_ , isFinSet→ X Y) ≡ card Y ^ card X
  card→ = cardΠ X (λ _ → Y) ∙ prodConst X (λ _ → card Y) (card Y) (λ _ → refl)

module _
  (X : FinSet ℓ ) where

  cardAut : card (_ , isFinSetAut X) ≡ LehmerCode.factorial (card X)
  cardAut = refl

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ')
  (f : X .fst → Y .fst) where

  sumCardFiber : card X ≡ sum Y (λ y → card (_ , isFinSetFiber X Y f y))
  sumCardFiber =
      cardEquiv X (_ , isFinSetΣ Y (λ y → _ , isFinSetFiber X Y f y)) ∣ totalEquiv f ∣
    ∙ cardΣ Y (λ y → _ , isFinSetFiber X Y f y)

-- the pigeonhole priniple

-- a logical lemma
private
  ¬ΠQ→¬¬ΣP : (X : Type ℓ)
      (P : X → Type ℓ' )
      (Q : X → Type ℓ'')
      (r : (x : X) → ¬ (P x) → Q x)
    → ¬ ((x : X) → Q x) → ¬ ¬ (Σ X P)
  ¬ΠQ→¬¬ΣP _ _ _ r g f = g (λ x → r x (λ p → f (x , p)))

module _
  (f : X .fst → Y .fst)
  (n : ℕ) where

  fiberCount : ((y : Y .fst) → card (_ , isFinSetFiber X Y f y) ≤ n) → card X ≤ n · card Y
  fiberCount h =
    subst (λ a → a ≤ _) (sym (sumCardFiber X Y f))
          (sumBounded Y (λ y → card (_ , isFinSetFiber X Y f y)) n h)

  module _
    (p : card X > n · card Y) where

    ¬¬pigeonHole : ¬ ¬ (Σ[ y ∈ Y .fst ] card (_ , isFinSetFiber X Y f y) > n)
    ¬¬pigeonHole =
      ¬ΠQ→¬¬ΣP (Y .fst) (λ y → _ > n) (λ y → _ ≤ n)
               (λ y → <-asym') (λ h → <-asym p (fiberCount h))

    pigeonHole : ∥ Σ[ y ∈ Y .fst ] card (_ , isFinSetFiber X Y f y) > n ∥
    pigeonHole = PeirceLaw (isFinSetΣ Y (λ _ → _ , isDecProp→isFinSet m≤n-isProp (≤Dec _ _))) ¬¬pigeonHole

-- a special case, proved in Cubical.Data.Fin.Properties

-- a technical lemma
private
  Σ∥P∥→∥ΣP∥ : (X : Type ℓ)(P : X → Type ℓ')
    → Σ X (λ x → ∥ P x ∥) → ∥ Σ X P ∥
  Σ∥P∥→∥ΣP∥ _ _ (x , p) = Prop.map (λ q → x , q) p

module _
  (f : X .fst → Y .fst)
  (p : card X > card Y) where

  fiberNonEqualTerm : Σ[ y ∈ Y .fst ] card (_ , isFinSetFiber X Y f y) > 1
    → ∥ Σ[ y ∈ Y .fst ] Σ[ a ∈ fiber f y ] Σ[ b ∈ fiber f y ] ¬ a ≡ b ∥
  fiberNonEqualTerm (y , p) = Σ∥P∥→∥ΣP∥ _ _ (y , card>1→hasNonEqualTerm {X = _ , isFinSetFiber X Y f y} p)

  nonInj : Σ[ y ∈ Y .fst ] Σ[ a ∈ fiber f y ] Σ[ b ∈ fiber f y ] ¬ a ≡ b
    → Σ[ x ∈ X .fst ] Σ[ x' ∈ X .fst ] (¬ x ≡ x') × (f x ≡ f x')
  nonInj (y , (x , p) , (x' , q) , t) .fst = x
  nonInj (y , (x , p) , (x' , q) , t) .snd .fst = x'
  nonInj (y , (x , p) , (x' , q) , t) .snd .snd .fst u =
    t (λ i → u i , isSet→SquareP (λ i j → isFinSet→isSet (Y .snd)) p q (cong f u) refl i)
  nonInj (y , (x , p) , (x' , q) , t) .snd .snd .snd = p ∙ sym q

  pigeonHole' : ∥ Σ[ x ∈ X .fst ] Σ[ x' ∈ X .fst ] (¬ x ≡ x') × (f x ≡ f x') ∥
  pigeonHole' =
    Prop.map nonInj
      (Prop.rec isPropPropTrunc fiberNonEqualTerm
        (pigeonHole {X = X} {Y = Y} f 1 (subst (λ a → _ > a) (sym (·-identityˡ _)) p)))

-- cardinality and injection/surjection

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  module _
    (f : X .fst → Y .fst) where

    card↪Inequality' : isEmbedding f → card X ≤ card Y
    card↪Inequality' p =
      subst2 (_≤_)
        (sym (sumCardFiber X Y f))
        (·-identityˡ _)
        (sumBounded Y (λ y → card (_ , isFinSetFiber X Y f y)) 1
          (λ y → isProp→card≤1 (_ , isFinSetFiber X Y f y)
            (isEmbedding→hasPropFibers p y)))

    card↠Inequality' : isSurjection f → card X ≥ card Y
    card↠Inequality' p =
      subst2 (_≥_)
        (sym (sumCardFiber X Y f))
        (·-identityˡ _)
        (sumBoundedBelow Y (λ y → card (_ , isFinSetFiber X Y f y)) 1
          (λ y → isInhab→card>0 (_ , isFinSetFiber X Y f y) (p y)))

  card↪Inequality : ∥ X .fst ↪ Y .fst ∥ → card X ≤ card Y
  card↪Inequality = Prop.rec m≤n-isProp (λ (f , p) → card↪Inequality' f p)

  card↠Inequality : ∥ X .fst ↠ Y .fst ∥ → card X ≥ card Y
  card↠Inequality = Prop.rec m≤n-isProp (λ (f , p) → card↠Inequality' f p)

-- maximal value of numerical functions

module _
  (X : Type ℓ)
  (f : X → ℕ) where

  module _
    (x : X) where

    isMax : Type ℓ
    isMax = (x' : X) → f x' ≤ f x

    isPropIsMax : isProp isMax
    isPropIsMax = isPropΠ (λ _ → m≤n-isProp)

  uniqMax : (x x' : X) → isMax x → isMax x' → f x ≡ f x'
  uniqMax x x' p q = ≤-antisym (q x) (p x')

  ΣMax : Type ℓ
  ΣMax = Σ[ x ∈ X ] isMax x

  ∃Max : Type ℓ
  ∃Max = ∥ ΣMax ∥

  ∃Max→maxValue : ∃Max → ℕ
  ∃Max→maxValue =
    SetElim.rec→Set
      isSetℕ (λ (x , p) → f x)
             (λ (x , p) (x' , q) → uniqMax x x' p q)

-- lemma about maximal value on sum type
module _
  (X : Type ℓ )
  (Y : Type ℓ')
  (f : X ⊎ Y → ℕ) where

  ΣMax⊎-case : ((x , p) : ΣMax X (f ∘ inl))((y , q) : ΣMax Y (f ∘ inr))
    → Trichotomy (f (inl x)) (f (inr y)) → ΣMax (X ⊎ Y) f
  ΣMax⊎-case (x , p) (y , q) (lt r) .fst = inr y
  ΣMax⊎-case (x , p) (y , q) (lt r) .snd (inl x') = ≤-trans (p x') (<-weaken r)
  ΣMax⊎-case (x , p) (y , q) (lt r) .snd (inr y') = q y'
  ΣMax⊎-case (x , p) (y , q) (eq r) .fst = inr y
  ΣMax⊎-case (x , p) (y , q) (eq r) .snd (inl x') = ≤-trans (p x') (_ , r)
  ΣMax⊎-case (x , p) (y , q) (eq r) .snd (inr y') = q y'
  ΣMax⊎-case (x , p) (y , q) (gt r) .fst = inl x
  ΣMax⊎-case (x , p) (y , q) (gt r) .snd (inl x') = p x'
  ΣMax⊎-case (x , p) (y , q) (gt r) .snd (inr y') = ≤-trans (q y') (<-weaken r)

  ∃Max⊎ : ∃Max X (f ∘ inl) → ∃Max Y (f ∘ inr) → ∃Max (X ⊎ Y) f
  ∃Max⊎ = Prop.map2 (λ p q → ΣMax⊎-case p q (_≟_ _ _))

ΣMax𝟙 : (f : 𝟙 {ℓ} .fst → ℕ) → ΣMax _ f
ΣMax𝟙 f .fst = tt*
ΣMax𝟙 f .snd x = _ , cong f (sym (isContrUnit* .snd x))

∃Max𝟙 : (f : 𝟙 {ℓ} .fst → ℕ) → ∃Max _ f
∃Max𝟙 f = ∣ ΣMax𝟙 f ∣

∃Max𝔽in : (n : ℕ)(f : 𝔽in {ℓ} n .fst → ℕ)(x : ∥ 𝔽in {ℓ} n .fst ∥) → ∃Max _ f
∃Max𝔽in {ℓ = ℓ} 0 _ x = Empty.rec (<→≢ (isInhab→card>0 (𝔽in 0) x) (card𝟘 {ℓ = ℓ}))
∃Max𝔽in 1 f _ =
  subst (λ X → (f : X .fst → ℕ) → ∃Max _ f) (sym 𝔽in1≡𝟙) ∃Max𝟙 f
∃Max𝔽in (suc (suc n)) f _ =
  ∃Max⊎ (𝟙 .fst) (𝔽in (suc n) .fst) f (∃Max𝟙 (f ∘ inl)) (∃Max𝔽in (suc n) (f ∘ inr) ∣ * {n = n} ∣)

module _
  (X : FinSet ℓ)
  (f : X .fst → ℕ)
  (x : ∥ X .fst ∥) where

  ∃MaxFinSet : ∃Max _ f
  ∃MaxFinSet =
    elimProp
      (λ X → (f : X .fst → ℕ)(x : ∥ X .fst ∥) → ∃Max _ f)
      (λ X → isPropΠ2 (λ _ _ → isPropPropTrunc)) ∃Max𝔽in X f x

  maxValue : ℕ
  maxValue = ∃Max→maxValue _ _ ∃MaxFinSet

{- some formal consequences of card -}

-- card induces equivalence from set truncation of FinSet to natural numbers

open Iso

Iso-∥FinSet∥₂-ℕ : Iso ∥ FinSet ℓ ∥₂ ℕ
Iso-∥FinSet∥₂-ℕ .fun = Set.rec isSetℕ card
Iso-∥FinSet∥₂-ℕ .inv n = ∣ 𝔽in n ∣₂
Iso-∥FinSet∥₂-ℕ .rightInv n = card𝔽in n
Iso-∥FinSet∥₂-ℕ {ℓ = ℓ} .leftInv =
  Set.elim {B = λ X → ∣ 𝔽in (Set.rec isSetℕ card X) ∣₂ ≡ X}
    (λ X → isSetPathImplicit)
    (elimProp (λ X → ∣ 𝔽in (card X) ∣₂ ≡ ∣ X ∣₂) (λ X → squash₂ _ _)
      (λ n i → ∣ 𝔽in (card𝔽in {ℓ = ℓ} n i) ∣₂))

-- this is the definition of natural numbers you learned from school
∥FinSet∥₂≃ℕ : ∥ FinSet ℓ ∥₂ ≃ ℕ
∥FinSet∥₂≃ℕ = isoToEquiv Iso-∥FinSet∥₂-ℕ

-- FinProp is equivalent to Bool

Bool→FinProp : Bool → FinProp ℓ
Bool→FinProp true = 𝟙 , isPropUnit*
Bool→FinProp false = 𝟘 , isProp⊥*

injBool→FinProp : (x y : Bool) → Bool→FinProp {ℓ = ℓ} x ≡ Bool→FinProp y → x ≡ y
injBool→FinProp true true _ = refl
injBool→FinProp false false _ = refl
injBool→FinProp true false p = Empty.rec (snotz (cong (card ∘ fst) p))
injBool→FinProp false true p = Empty.rec (znots (cong (card ∘ fst) p))

isEmbeddingBool→FinProp : isEmbedding (Bool→FinProp {ℓ = ℓ})
isEmbeddingBool→FinProp = injEmbedding isSetBool isSetFinProp (λ {x} {y} → injBool→FinProp x y)

card-case : (P : FinProp ℓ) → {n : ℕ} → card (P .fst) ≡ n → Σ[ x ∈ Bool ] Bool→FinProp x ≡ P
card-case P {n = 0} p = false , FinProp≡ (𝟘 , isProp⊥*) P .fst (cong fst (sym (card≡0 {X = P .fst} p)))
card-case P {n = 1} p = true , FinProp≡ (𝟙 , isPropUnit*) P .fst (cong fst (sym (card≡1 {X = P .fst} p)))
card-case P {n = suc (suc n)} p =
  Empty.rec (¬-<-zero (pred-≤-pred (subst (λ a → a ≤ 1) p (isProp→card≤1 (P .fst) (P .snd)))))

isSurjectionBool→FinProp : isSurjection (Bool→FinProp {ℓ = ℓ})
isSurjectionBool→FinProp P = ∣ card-case P refl ∣

FinProp≃Bool : FinProp ℓ ≃ Bool
FinProp≃Bool =
  invEquiv (Bool→FinProp ,
    isEmbedding×isSurjection→isEquiv (isEmbeddingBool→FinProp  , isSurjectionBool→FinProp))

isFinSetFinProp : isFinSet (FinProp ℓ)
isFinSetFinProp = EquivPresIsFinSet (invEquiv FinProp≃Bool) isFinSetBool

-- a more computationally efficient version of equivalence type

module _
  (X : FinSet ℓ )
  (Y : FinSet ℓ') where

  isFinSet≃Eff' : Dec (card X ≡ card Y) → isFinSet (X .fst ≃ Y .fst)
  isFinSet≃Eff' (yes p) = factorial (card Y) ,
    Prop.elim2 (λ _ _ → isPropPropTrunc {A = _ ≃ Fin _})
      (λ p1 p2
        → ∣ equivComp (p1 ⋆ pathToEquiv (cong Fin p) ⋆ SumFin≃Fin _) (p2 ⋆ SumFin≃Fin _)
          ⋆ lehmerEquiv ⋆ lehmerFinEquiv
          ⋆ invEquiv (SumFin≃Fin _) ∣)
      (∣≃card∣ X) (∣≃card∣ Y)
  isFinSet≃Eff' (no ¬p) = 0 , ∣ uninhabEquiv (¬p ∘ cardEquiv X Y ∘ ∣_∣) (idfun _) ∣

  isFinSet≃Eff : isFinSet (X .fst ≃ Y .fst)
  isFinSet≃Eff = isFinSet≃Eff' (discreteℕ _ _)

module _
  (X Y : FinSet ℓ) where

  isFinSetType≡Eff : isFinSet (X .fst ≡ Y .fst)
  isFinSetType≡Eff = EquivPresIsFinSet (invEquiv univalence) (isFinSet≃Eff X Y)
