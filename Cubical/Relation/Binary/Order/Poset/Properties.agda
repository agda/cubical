{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Properties where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Proset
open import Cubical.Relation.Binary.Order.Quoset.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→isProset : IsPoset R → IsProset R
  isPoset→isProset poset = isproset
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  isPosetDecidable→Discrete : IsPoset R → isDecidable R → Discrete A
  isPosetDecidable→Discrete pos dec a b with dec a b
  ... | no ¬Rab = no (λ a≡b → ¬Rab (subst (R a) a≡b (IsPoset.is-refl pos a)))
  ... | yes Rab with dec b a
  ...       | no ¬Rba = no (λ a≡b → ¬Rba (subst (λ x → R x a) a≡b
                                         (IsPoset.is-refl pos a)))
  ...       | yes Rba = yes (IsPoset.is-antisym pos a b Rab Rba)

  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isPoset→isQuosetIrreflKernel : IsPoset R → IsQuoset (IrreflKernel R)
  isPoset→isQuosetIrreflKernel poset
    = isquoset (IsPoset.is-set poset)
                    (λ a b → isProp× (IsPoset.is-prop-valued poset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsPoset.is-trans poset)
                                 (IsPoset.is-antisym poset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsPoset.is-trans poset)
                                                           (IsPoset.is-antisym poset)))

  isPosetDecidable→isQuosetDecidable : IsPoset R → isDecidable R → isDecidable (IrreflKernel R)
  isPosetDecidable→isQuosetDecidable pos dec a b with dec a b
  ... | no ¬Rab = no λ { (Rab , _) → ¬Rab Rab }
  ... | yes Rab with (isPosetDecidable→Discrete pos dec) a b
  ...       | yes a≡b = no λ { (_ , ¬a≡b) → ¬a≡b a≡b }
  ...       | no a≢b = yes (Rab , a≢b)

  isPosetInduced : IsPoset R → (B : Type ℓ'') → (f : B ↪ A) → IsPoset (InducedRelation R (B , f))
  isPosetInduced pos B (f , emb)
    = isposet (Embedding-into-isSet→isSet (f , emb) (IsPoset.is-set pos))
              (λ a b → IsPoset.is-prop-valued pos (f a) (f b))
              (λ a → IsPoset.is-refl pos (f a))
              (λ a b c → IsPoset.is-trans pos (f a) (f b) (f c))
              λ a b a≤b b≤a → isEmbedding→Inj emb a b
                (IsPoset.is-antisym pos (f a) (f b) a≤b b≤a)

Poset→Proset : Poset ℓ ℓ' → Proset ℓ ℓ'
Poset→Proset (_ , pos) = _ , prosetstr (PosetStr._≤_ pos)
                                           (isPoset→isProset (PosetStr.isPoset pos))

module PosetDownset (P' : Poset ℓ ℓ') where
  private P = fst P'
  open PosetStr (snd P')

  ↓ : P → Type (ℓ-max ℓ ℓ')
  ↓ u = Σ[ v ∈ P ] v ≤ u

  ↓ᴾ : P → Poset (ℓ-max ℓ ℓ') ℓ'
  fst (↓ᴾ u) = ↓ u
  PosetStr._≤_ (snd (↓ᴾ u)) v w = v .fst ≤ w .fst
  PosetStr.isPoset (snd (↓ᴾ u)) =
    isPosetInduced
      (PosetStr.isPoset (snd P'))
      _
      (EmbeddingΣProp (λ a → is-prop-valued _ _))

Poset→Quoset : Poset ℓ ℓ' → Quoset ℓ (ℓ-max ℓ ℓ')
Poset→Quoset (_ , pos)
  = _ , quosetstr (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
                       (isPoset→isQuosetIrreflKernel (PosetStr.isPoset pos))

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (pos : IsPoset _≤_)
  where

  private
      pre = isPoset→isProset pos  

      prop = IsPoset.is-prop-valued pos

      rfl = IsPoset.is-refl pos

      anti = IsPoset.is-antisym pos

      trans = IsPoset.is-trans pos

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

  isBoundedAbove : Type (ℓ-max ℓ ℓ')
  isBoundedAbove = Greatest pre (A , (id↪ A))

  isBoundedBelow : Type (ℓ-max ℓ ℓ')
  isBoundedBelow = Least pre (A , id↪ A)

  isBounded : Type (ℓ-max ℓ ℓ')
  isBounded = isBoundedBelow × isBoundedAbove

  isPropIsBoundedAbove : isProp isBoundedAbove
  isPropIsBoundedAbove (x , gtx) (y , gty)
    = Σ≡Prop (λ _ → isPropIsGreatest pre (A , (id↪ A)) _)
              (isGreatestUnique {P = A , (id↪ A)} x y gtx gty)

  isPropIsBoundedBelow : isProp isBoundedBelow
  isPropIsBoundedBelow (x , ltx) (y , lty)
    = Σ≡Prop (λ _ → isPropIsLeast pre (A , id↪ A) _)
              (isLeastUnique {P = A , id↪ A} x y ltx lty)

  isPropIsBounded : isProp isBounded
  isPropIsBounded = isProp× isPropIsBoundedBelow isPropIsBoundedAbove
