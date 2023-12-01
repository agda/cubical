{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

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
      prop = IsPreorder.is-prop-valued pre

  module _
    (P : Embedding A ℓ'')
    where

    private
      subtype = fst P

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
    pre = isPoset→isPreorder pos

    anti = IsPoset.is-antisym pos

  module _
    {P : Embedding A ℓ''}
    where

    private
      toA = fst (snd P)

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
    prop = IsToset.is-prop-valued tos

    total = IsToset.is-total tos

    pre = isPoset→isPreorder (isToset→isPoset tos)

    toA = fst (snd P)

  isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
  isMinimal→isLeast n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (total (toA n) (toA m))

  isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
  isMaximal→isGreatest n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (total (toA n) (toA m))

-- Defining meets and joins as operators on preorders so that lattice structures on orders are easier to define
module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  where

    isMeet : IsPreorder _≤_ → A → A → A → Type (ℓ-max ℓ ℓ')
    isMeet _ a b c = ∀ x → x ≤ c ≃ (x ≤ a × x ≤ b)

    isJoin : IsPreorder _≤_ → A → A → A → Type (ℓ-max ℓ ℓ')
    isJoin _ a b c = ∀ x → c ≤ x ≃ (a ≤ x × b ≤ x)

    module _
      (pre : IsPreorder _≤_)
      where
        private
          prop = IsPreorder.is-prop-valued pre

          rfl = IsPreorder.is-refl pre

          trans = IsPreorder.is-trans pre

        Meet : ∀ a b → Type (ℓ-max ℓ ℓ')
        Meet a b = Σ[ a∧b ∈ A ] isMeet pre a b a∧b

        Join : ∀ a b → Type (ℓ-max ℓ ℓ')
        Join a b = Σ[ a∨b ∈ A ] isJoin pre a b a∨b

        isPropIsMeet : ∀ a b c → isProp (isMeet pre a b c)
        isPropIsMeet a b c = isPropΠ λ x → isOfHLevel≃ 1 (prop x c)
                                                          (isProp× (prop x a)
                                                                   (prop x b))

        isPropIsJoin : ∀ a b c → isProp (isJoin pre a b c)
        isPropIsJoin a b c = isPropΠ λ x → isOfHLevel≃ 1 (prop c x)
                                                          (isProp× (prop a x)
                                                                   (prop b x))

        isReflIsMeet : ∀ a → isMeet pre a a a
        isReflIsMeet a x = propBiimpl→Equiv (prop x a)
                                            (isProp× (prop x a) (prop x a))
                                            (λ a → a , a)
                                             fst

        isReflIsJoin : ∀ a → isJoin pre a a a
        isReflIsJoin a x = propBiimpl→Equiv (prop a x)
                                            (isProp× (prop a x) (prop a x))
                                            (λ a → a , a)
                                             fst

        isMeet≃isInfimum : ∀ a b c
                         → isMeet pre a b c
                         ≃ isInfimum pre {B = Σ[ x ∈ A ] (x ≡ a) ⊎ (x ≡ b)} fst c
        isMeet≃isInfimum a b a∧b
          = propBiimpl→Equiv (isPropIsMeet a b a∧b) (isPropIsInfimum pre fst a∧b)
                             (λ fun → ⊎.rec (λ x≡a → subst
                                                     (a∧b ≤_)
                                                     (sym x≡a)
                                                     (fun a∧b .fst (rfl a∧b) .fst))
                                            (λ x≡b → subst
                                                     (a∧b ≤_)
                                                     (sym x≡b)
                                                     (fun a∧b .fst (rfl a∧b) .snd))
                                      ∘ snd ,
                              λ { (c , uprc)
                                → invEq (fun c) ((uprc (a , (inl refl))) ,
                                                 (uprc (b , (inr refl)))) })
                              λ { (lb , gt) x
                                → propBiimpl→Equiv
                                 (prop x a∧b)
                                 (isProp× (prop x a) (prop x b))
                             (λ x≤a∧b → (trans x a∧b a x≤a∧b
                                               (lb (a , inl refl))) ,
                                         (trans x a∧b b x≤a∧b
                                               (lb (b , inr refl))))
                              λ { (x≤a , x≤b)
                                → gt (x ,
                                     (⊎.rec (λ y≡a → subst
                                                     (x ≤_)
                                                     (sym y≡a)
                                                      x≤a)
                                            (λ y≡b → subst
                                                     (x ≤_)
                                                     (sym y≡b)
                                                      x≤b)
                                             ∘ snd)) } }

        isJoin≃isSupremum : ∀ a b c
                          → isJoin pre a b c
                          ≃ isSupremum pre {B = Σ[ x ∈ A ] (x ≡ a) ⊎ (x ≡ b)} fst c
        isJoin≃isSupremum a b a∨b
          = propBiimpl→Equiv (isPropIsJoin a b a∨b) (isPropIsSupremum pre fst a∨b)
                             (λ fun → ⊎.rec (λ x≡a → subst
                                                     (_≤ a∨b)
                                                     (sym x≡a)
                                                     (fun a∨b .fst (rfl a∨b) .fst))
                                            (λ x≡b → subst
                                                     (_≤ a∨b)
                                                     (sym x≡b)
                                                     (fun a∨b .fst (rfl a∨b) .snd))
                                      ∘ snd ,
                              λ { (c , lwrc)
                                → invEq (fun c) ((lwrc (a , (inl refl))) ,
                                                 (lwrc (b , (inr refl)))) })
                              λ { (ub , lt) x
                                → propBiimpl→Equiv
                                 (prop a∨b x)
                                 (isProp× (prop a x) (prop b x))
                             (λ a∨b≤x → trans a a∨b x
                                              (ub (a , inl refl))
                                               a∨b≤x ,
                                         trans b a∨b x
                                              (ub (b , inr refl))
                                               a∨b≤x)
                              λ { (a≤x , b≤x)
                                → lt (x ,
                                     (⊎.rec (λ y≡a → subst
                                                     (_≤ x)
                                                     (sym y≡a)
                                                      a≤x)
                                            (λ y≡b → subst
                                                     (_≤ x)
                                                     (sym y≡b)
                                                      b≤x)
                                      ∘ snd)) } }

        isMeetComm : ∀ a b a∧b → isMeet pre a b a∧b → isMeet pre b a a∧b
        isMeetComm _ _ _ fun x = compEquiv (fun x) Σ-swap-≃

        isJoinComm : ∀ a b a∨b → isJoin pre a b a∨b → isJoin pre b a a∨b
        isJoinComm _ _ _ fun x = compEquiv (fun x) Σ-swap-≃

        isMeetAssoc : ∀ a b c a∧b b∧c a∧b∧c
                    → isMeet pre a b a∧b
                    → isMeet pre b c b∧c
                    → isMeet pre a b∧c a∧b∧c
                    → isMeet pre a∧b c a∧b∧c
        isMeetAssoc a b c a∧b b∧c a∧b∧c funa∧b funb∧c funa∧b∧c x
          = compEquiv (funa∧b∧c x)
                      (propBiimpl→Equiv (isProp× (prop x a) (prop x b∧c))
                                        (isProp× (prop x a∧b) (prop x c))
                                        (λ { (x≤a , x≤b∧c)
                                           → invEq (funa∧b x)
                                                   (x≤a ,
                                                   (funb∧c x .fst x≤b∧c .fst)) ,
                                                    funb∧c x .fst x≤b∧c .snd })
                                        λ { (x≤a∧b , x≤c)
                                          → funa∧b x .fst x≤a∧b .fst ,
                                            invEq (funb∧c x)
                                                 ((funa∧b x .fst x≤a∧b .snd) ,
                                                   x≤c) })

        isJoinAssoc : ∀ a b c a∨b b∨c a∨b∨c
                    → isJoin pre a b a∨b
                    → isJoin pre b c b∨c
                    → isJoin pre a b∨c a∨b∨c
                    → isJoin pre a∨b c a∨b∨c
        isJoinAssoc a b c a∨b b∨c a∨b∨c funa∨b funb∨c funa∨b∨c x
          = compEquiv (funa∨b∨c x)
                      (propBiimpl→Equiv (isProp× (prop a x) (prop b∨c x))
                                        (isProp× (prop a∨b x) (prop c x))
                                        (λ { (a≤x , b∨c≤x)
                                           → invEq (funa∨b x) (a≤x ,
                                           (funb∨c x .fst b∨c≤x .fst)) ,
                                            funb∨c x .fst b∨c≤x .snd })
                                         λ { (a∨b≤x , c≤x)
                                           → funa∨b x .fst a∨b≤x .fst ,
                                             invEq (funb∨c x)
                                           ((funa∨b x .fst a∨b≤x .snd) ,
                                             c≤x) })

    module _
      (pos : IsPoset _≤_)
      where
        private
          pre = isPoset→isPreorder pos

          prop = IsPoset.is-prop-valued pos

          rfl = IsPoset.is-refl pos

          anti = IsPoset.is-antisym pos

          trans = IsPoset.is-trans pos

        isMeetUnique : ∀ a b x y → isMeet pre a b x → isMeet pre a b y → x ≡ y
        isMeetUnique a b x y infx infy = anti x y x≤y y≤x
          where x≤y : x ≤ y
                x≤y = invEq (infy x) (infx x .fst (rfl x))

                y≤x : y ≤ x
                y≤x = invEq (infx y) (infy y .fst (rfl y))

        isJoinUnique : ∀ a b x y → isJoin pre a b x → isJoin pre a b y → x ≡ y
        isJoinUnique a b x y supx supy = anti x y x≤y y≤x
                where x≤y : x ≤ y
                      x≤y = invEq (supx y) (supy y .fst (rfl y))

                      y≤x : y ≤ x
                      y≤x = invEq (supy x) (supx x .fst (rfl x))

        MeetUnique : ∀ a b → (x y : Meet pre a b) → x ≡ y
        MeetUnique a b (x , mx) (y , my) = Σ≡Prop (isPropIsMeet pre a b)
                                                   (isMeetUnique a b x y mx my)

        JoinUnique : ∀ a b → (x y : Join pre a b) → x ≡ y
        JoinUnique a b (x , jx) (y , jy) = Σ≡Prop (isPropIsJoin pre a b)
                                                   (isJoinUnique a b x y jx jy)

        module _
          (meet : ∀ a b → Meet pre a b)
          where

            meetIdemp : ∀ a → meet a a .fst ≡ a
            meetIdemp a
              = PathPΣ (MeetUnique a a (meet a a)
                                       (a , (isReflIsMeet pre a))) .fst

            meetComm : ∀ a b → meet a b .fst ≡ meet b a .fst
            meetComm a b = sym (PathPΣ (MeetUnique b a (meet b a)
                                                 ((meet a b .fst) ,
                                                  (isMeetComm pre a b
                                                             (meet a b .fst)
                                                             (meet a b .snd)))) .fst)

            meetAssoc : ∀ a b c
                      → meet a (meet b c .fst) .fst ≡ meet (meet a b .fst) c .fst
            meetAssoc a b c
              = sym (PathPΣ (MeetUnique
                                (meet a b .fst) c
                                (meet (meet a b .fst) c)
                               ((meet a (meet b c .fst) .fst) ,
                                (isMeetAssoc pre a b c
                                            (meet a b .fst)
                                            (meet b c .fst)
                                            (meet a (meet b c .fst) .fst)
                                            (meet a b .snd)
                                            (meet b c .snd)
                                            (meet a (meet b c .fst) .snd)))) .fst)

        module _
          (join : ∀ a b → Join pre a b)
          where

            joinIdem : ∀ a → join a a .fst ≡ a
            joinIdem a
              = PathPΣ (JoinUnique a a (join a a)
                                       (a , (isReflIsJoin pre a))) .fst

            joinComm : ∀ a b → join a b .fst ≡ join b a .fst
            joinComm a b = sym (PathPΣ (JoinUnique b a (join b a)
                                                 ((join a b .fst) ,
                                                  (isJoinComm pre a b
                                                             (join a b .fst)
                                                             (join a b .snd)))) .fst)

            joinAssoc : ∀ a b c
                      → join a (join b c .fst) .fst ≡ join (join a b .fst) c .fst
            joinAssoc a b c
              = sym (PathPΣ (JoinUnique
                                (join a b .fst) c
                                (join (join a b .fst) c)
                               ((join a (join b c .fst) .fst) ,
                                (isJoinAssoc pre a b c
                                            (join a b .fst)
                                            (join b c .fst)
                                            (join a (join b c .fst) .fst)
                                            (join a b .snd)
                                            (join b c .snd)
                                            (join a (join b c .fst) .snd)))) .fst)
