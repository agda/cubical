{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset
open import Cubical.Relation.Binary.Order.Preorder.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsPreorder _≲_)
  where

  private
      prop : ∀ a b → isProp (a ≲ b)
      prop = IsPreorder.is-prop-valued pre

  module _
    (P : Embedding A ℓ'')
    where

    private
      subtype : Type ℓ''
      subtype = fst P

      toA : subtype → A
      toA = fst (snd P)

    isMinimal : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isMinimal n = (x : subtype) → toA x ≲ toA n → toA n ≲ toA x

    isPropIsMinimal : ∀ n → isProp (isMinimal n)
    isPropIsMinimal n = isPropΠ2 λ x _ → prop (toA n) (toA x)

    Minimal : Type (ℓ-max ℓ' ℓ'')
    Minimal = Σ[ n ∈ subtype ] isMinimal n

    isMaximal : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isMaximal n = (x : subtype) → toA n ≲ toA x → toA x ≲ toA n

    isPropIsMaximal : ∀ n → isProp (isMaximal n)
    isPropIsMaximal n = isPropΠ2 λ x _ → prop (toA x) (toA n)

    Maximal : Type (ℓ-max ℓ' ℓ'')
    Maximal = Σ[ n ∈ subtype ] isMaximal n

    isLeast : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isLeast n = (x : subtype) → toA n ≲ toA x

    isPropIsLeast : ∀ n → isProp (isLeast n)
    isPropIsLeast n = isPropΠ λ x → prop (toA n) (toA x)

    Least : Type (ℓ-max ℓ' ℓ'')
    Least = Σ[ n ∈ subtype ] isLeast n

    isGreatest : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isGreatest n = (x : subtype) → toA x ≲ toA n

    isPropIsGreatest : ∀ n → isProp (isGreatest n)
    isPropIsGreatest n = isPropΠ λ x → prop (toA x) (toA n)

    Greatest : Type (ℓ-max ℓ' ℓ'')
    Greatest = Σ[ n ∈ subtype ] isGreatest n

  module _
    {B : Type ℓ''}
    (P : B → A)
    where

    isLowerBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isLowerBound n = (x : B) → n ≲ P x

    isPropIsLowerBound : ∀ n → isProp (isLowerBound n)
    isPropIsLowerBound n = isPropΠ λ x → prop n (P x)

    LowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    LowerBound = Σ[ n ∈ A ] isLowerBound n

    isUpperBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isUpperBound n = (x : B) → P x ≲ n

    isPropIsUpperBound : ∀ n → isProp (isUpperBound n)
    isPropIsUpperBound n = isPropΠ λ x → prop (P x) n

    UpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    UpperBound = Σ[ n ∈ A ] isUpperBound n

  module _
    {B : Type ℓ''}
    (P : B → A)
    where

    isMaximalLowerBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMaximalLowerBound n
      = Σ[ islb ∈ isLowerBound P n ]
        isMaximal (LowerBound P
                  , (EmbeddingΣProp (isPropIsLowerBound P))) (n , islb)

    isPropIsMaximalLowerBound : ∀ n → isProp (isMaximalLowerBound n)
    isPropIsMaximalLowerBound n
      = isPropΣ (isPropIsLowerBound P n)
                λ islb → isPropIsMaximal (LowerBound P
                       , EmbeddingΣProp (isPropIsLowerBound P)) (n , islb)

    MaximalLowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    MaximalLowerBound = Σ[ n ∈ A ] isMaximalLowerBound n

    isMinimalUpperBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMinimalUpperBound n
      = Σ[ isub ∈ isUpperBound P n ]
        isMinimal (UpperBound P
                  , EmbeddingΣProp (isPropIsUpperBound P)) (n , isub)

    isPropIsMinimalUpperBound : ∀ n → isProp (isMinimalUpperBound n)
    isPropIsMinimalUpperBound n
      = isPropΣ (isPropIsUpperBound P n)
                λ isub → isPropIsMinimal (UpperBound P
                       , EmbeddingΣProp (isPropIsUpperBound P)) (n , isub)

    MinimalUpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    MinimalUpperBound = Σ[ n ∈ A ] isMinimalUpperBound n

    isInfimum : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isInfimum n
      = Σ[ islb ∈ isLowerBound P n ]
        isGreatest (LowerBound P
                   , EmbeddingΣProp (isPropIsLowerBound P)) (n , islb)

    isPropIsInfimum : ∀ n → isProp (isInfimum n)
    isPropIsInfimum n
      = isPropΣ (isPropIsLowerBound P n)
                λ islb → isPropIsGreatest (LowerBound P
                       , EmbeddingΣProp (isPropIsLowerBound P)) (n , islb)

    Infimum : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Infimum = Σ[ n ∈ A ] isInfimum n

    isSupremum : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isSupremum n
      = Σ[ isub ∈ isUpperBound P n ]
        isLeast (UpperBound P
                , EmbeddingΣProp (isPropIsUpperBound P)) (n , isub)

    isPropIsSupremum : ∀ n → isProp (isSupremum n)
    isPropIsSupremum n
      = isPropΣ (isPropIsUpperBound P n)
                λ isub → isPropIsLeast (UpperBound P
                       , EmbeddingΣProp (isPropIsUpperBound P)) (n , isub)

    Supremum : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Supremum = Σ[ n ∈ A ] isSupremum n

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsPreorder _≲_)
  where

  module _
    {P : Embedding A ℓ''}
    where

    private
      toA : (fst P) → A
      toA = fst (snd P)

    isLeast→isMinimal : ∀ n → isLeast pre P n → isMinimal pre P n
    isLeast→isMinimal _ isl x _ = isl x

    isGreatest→isMaximal : ∀ n → isGreatest pre P n → isMaximal pre P n
    isGreatest→isMaximal _ isg x _ = isg x

    isLeast→isLowerBound : ∀ n → isLeast pre P n → isLowerBound pre toA (toA n)
    isLeast→isLowerBound _ isl = isl

    isGreatest→isUpperBound : ∀ n → isGreatest pre P n → isUpperBound pre toA (toA n)
    isGreatest→isUpperBound _ isg = isg

    isLeast→isInfimum : ∀ n → isLeast pre P n → isInfimum pre toA (toA n)
    isLeast→isInfimum n isl = (isLeast→isLowerBound n isl) , (λ x → snd x n)

    isGreatest→isSupremum : ∀ n → isGreatest pre P n → isSupremum pre toA (toA n)
    isGreatest→isSupremum n isg = (isGreatest→isUpperBound n isg) , (λ x → snd x n)

  module _
    {B : Type ℓ''}
    {P : B → A}
    where

    isInfimum→isLowerBound : ∀ n → isInfimum pre P n → isLowerBound pre P n
    isInfimum→isLowerBound _ = fst

    isSupremum→isUpperBound : ∀ n → isSupremum pre P n → isUpperBound pre P n
    isSupremum→isUpperBound _ = fst

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (pos : IsPoset _≤_)
  where

  private
    pre : IsPreorder _≤_
    pre = isPoset→isPreorder pos

    anti : BinaryRelation.isAntisym _≤_
    anti = IsPoset.is-antisym pos

  module _
    {P : Embedding A ℓ''}
    where

    private
      toA : (fst P) → A
      toA = fst (snd P)

      emb : isEmbedding toA
      emb = snd (snd P)

    isLeast→ContrMinimal : ∀ n → isLeast pre P n  → ∀ m → isMinimal pre P m → n ≡ m
    isLeast→ContrMinimal n isln m ismm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isln m) (ismm n (isln m)))

    isGreatest→ContrMaximal : ∀ n → isGreatest pre P n → ∀ m → isMaximal pre P m → n ≡ m
    isGreatest→ContrMaximal n isgn m ismm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (ismm n (isgn m)) (isgn m))

    isLeastUnique : ∀ n m → isLeast pre P n → isLeast pre P m → n ≡ m
    isLeastUnique n m isln islm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isln m) (islm n))

    isGreatestUnique : ∀ n m → isGreatest pre P n → isGreatest pre P m → n ≡ m
    isGreatestUnique n m isgn isgm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isgm n) (isgn m))

  module _
    {B : Type ℓ''}
    {P : B → A}
    where

    isInfimum→ContrMaximalLowerBound : ∀ n → isInfimum pre P n
                                     → ∀ m → isMaximalLowerBound pre P m
                                     → n ≡ m
    isInfimum→ContrMaximalLowerBound n (isln , isglbn) m (islm , ismlbm)
      = anti n m (ismlbm (n , isln) (isglbn (m , islm))) (isglbn (m , islm))

    isSupremum→ContrMinimalUpperBound : ∀ n → isSupremum pre P n
                                      → ∀ m → isMinimalUpperBound pre P m
                                      → n ≡ m
    isSupremum→ContrMinimalUpperBound n (isun , islubn) m (isum , ismubm)
      = anti n m (islubn (m , isum)) (ismubm (n , isun) (islubn (m , isum)))

    isInfimumUnique : ∀ n m → isInfimum pre P n → isInfimum pre P m → n ≡ m
    isInfimumUnique n m (isln , infn) (islm , infm)
      = anti n m (infm (n , isln)) (infn (m , islm))

    isSupremumUnique : ∀ n m → isSupremum pre P n → isSupremum pre P m → n ≡ m
    isSupremumUnique n m (isun , supn) (isum , supm)
      = anti n m (supn (m , isum)) (supm (n , isun))

module _
  {A : Type ℓ}
  {P : Embedding A ℓ''}
  {_≤_ : Rel A A ℓ'}
  (tos : IsToset _≤_)
  where

  private
    prop : ∀ a b → isProp (a ≤ b)
    prop = IsToset.is-prop-valued tos

    conn : BinaryRelation.isStronglyConnected _≤_
    conn = IsToset.is-strongly-connected tos

    pre : IsPreorder _≤_
    pre = isPoset→isPreorder (isToset→isPoset tos)

    toA : (fst P) → A
    toA = fst (snd P)

  isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
  isMinimal→isLeast n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (conn (toA n) (toA m))

  isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
  isMaximal→isGreatest n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (conn (toA n) (toA m))
