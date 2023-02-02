{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.StrictPoset
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→IsPreorder : IsPoset R → IsPreorder R
  isPoset→IsPreorder poset = ispreorder
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  isToset→IsPoset : IsToset R → IsPoset R
  isToset→IsPoset toset = isposet
                          (IsToset.is-set toset)
                          (IsToset.is-prop-valued toset)
                          (IsToset.is-refl toset)
                          (IsToset.is-trans toset)
                          (IsToset.is-antisym toset)

  isLoset→IsStrictPoset : IsLoset R → IsStrictPoset R
  isLoset→IsStrictPoset loset = isstrictposet
                                (IsLoset.is-set loset)
                                (IsLoset.is-prop-valued loset)
                                (IsLoset.is-irrefl loset)
                                (IsLoset.is-trans loset)
                                (IsLoset.is-asym loset)

  private
    -- Some lemmas that otherwise repeat several times
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

    transrefl : isTrans R → isTrans (ReflClosure R)
    transrefl trans a b c (inl Rab) (inl Rbc) = inl (trans a b c Rab Rbc)
    transrefl trans a b c (inl Rab) (inr b≡c) = inl (subst (R a) b≡c Rab)
    transrefl trans a b c (inr a≡b) (inl Rbc) = inl (subst (λ z → R z c) (sym a≡b) Rbc)
    transrefl trans a b c (inr a≡b) (inr b≡c) = inr (a≡b ∙ b≡c)

    antisym : isIrrefl R → isTrans R → isAntisym (ReflClosure R)
    antisym irr trans a b (inl Rab) (inl Rba) = ⊥.rec (irr a (trans a b a Rab Rba))
    antisym irr trans a b (inl _) (inr b≡a) = sym b≡a
    antisym irr trans a b (inr a≡b) _ = a≡b

  isPoset→IsStrictPosetIrreflKernel : IsPoset R → IsStrictPoset (IrreflKernel R)
  isPoset→IsStrictPosetIrreflKernel poset
    = isstrictposet (IsPoset.is-set poset)
                    (λ a b → isProp× (IsPoset.is-prop-valued poset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsPoset.is-trans poset)
                                 (IsPoset.is-antisym poset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsPoset.is-trans poset)
                                                           (IsPoset.is-antisym poset)))

  isToset→IsLosetIrreflKernel : Discrete A → IsToset R → IsLoset (IrreflKernel R)
  isToset→IsLosetIrreflKernel disc toset
    = isloset (IsToset.is-set toset)
              (λ a b → isProp× (IsToset.is-prop-valued toset a b)
                               (isProp¬ (a ≡ b)))
              (isIrreflIrreflKernel R)
              (transirrefl (IsToset.is-trans toset)
                           (IsToset.is-antisym toset))
              (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                       (isIrreflIrreflKernel R
                                       , transirrefl (IsToset.is-trans toset)
                                                     (IsToset.is-antisym toset)))
              (λ a c b (Rac , ¬a≡c)
                → decRec (λ a≡b → ∥₁.map (⊎.rec
                         (λ Rbc → inr (Rbc , λ b≡c → ¬a≡c (a≡b ∙ b≡c)))
                                λ Rcb → ⊥.rec (¬a≡c (IsToset.is-antisym toset a c Rac
                                              (subst (λ x → R c x) (sym a≡b) Rcb))))
                                  (IsToset.is-strongly-connected toset b c))
                         (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → Rab , ¬a≡b)
                                   (λ Rba → (IsToset.is-trans toset b a c Rba Rac)
                                   , λ b≡c → ¬a≡b (IsToset.is-antisym toset a b
                                       (subst (λ x → R a x) (sym b≡c) Rac) Rba)))
                                 (IsToset.is-strongly-connected toset a b))
                         (disc a b))
              (isConnectedStronglyConnectedIrreflKernel R
                (IsToset.is-strongly-connected toset))

  isStrictPoset→IsPosetReflClosure : IsStrictPoset R → IsPoset (ReflClosure R)
  isStrictPoset→IsPosetReflClosure strictposet
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

  isLoset→IsTosetReflClosure : Discrete A → IsLoset R → IsToset (ReflClosure R)
  isLoset→IsTosetReflClosure disc loset
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

  isPreorder→IsEquivRelSymKernel : IsPreorder R → isEquivRel (SymKernel R)
  isPreorder→IsEquivRelSymKernel preorder
    = equivRel (λ a → (IsPreorder.is-refl preorder a)
                    , (IsPreorder.is-refl preorder a))
               (isSymSymKernel R)
               (λ a b c (Rab , Rba) (Rbc , Rcb)
                 → IsPreorder.is-trans preorder a b c Rab Rbc
                 , IsPreorder.is-trans preorder c b a Rcb Rba)

  isPreorder→IsStrictPosetAsymKernel : IsPreorder R → IsStrictPoset (AsymKernel R)
  isPreorder→IsStrictPosetAsymKernel preorder
    = isstrictposet (IsPreorder.is-set preorder)
                    (λ a b → isProp× (IsPreorder.is-prop-valued preorder a b) (isProp¬ (R b a)))
                    (λ a (Raa , ¬Raa) → ¬Raa (IsPreorder.is-refl preorder a))
                    (λ a b c (Rab , ¬Rba) (Rbc , ¬Rcb)
                      → IsPreorder.is-trans preorder a b c Rab Rbc
                      , λ Rca → ¬Rcb (IsPreorder.is-trans preorder c a b Rca Rab))
                    (isAsymAsymKernel R)

  isStrictPoset→IsApartnessSymClosure : IsStrictPoset R
                                      → isWeaklyLinear R
                                      → IsApartness (SymClosure R)
  isStrictPoset→IsApartnessSymClosure strictposet weak
    = isapartness (IsStrictPoset.is-set strictposet)
                  (λ a b → isProp⊎ (IsStrictPoset.is-prop-valued strictposet a b)
                                   (IsStrictPoset.is-prop-valued strictposet b a)
                                   (IsStrictPoset.is-asym strictposet a b))
                  (λ a x → ⊎.rec (IsStrictPoset.is-irrefl strictposet a)
                                 (IsStrictPoset.is-irrefl strictposet a) x)
                  (λ a b c x → ⊎.rec (λ Rab → ∥₁.map (⊎.map (λ Rac → inl Rac)
                                                             (λ Rcb → inr Rcb))
                                                      (weak a b c Rab))
                                     (λ Rba → ∥₁.rec squash₁
                                                     (λ y → ∣ ⊎.rec (λ Rbc → inr (inl Rbc))
                                                     (λ Rca → inl (inr Rca)) y ∣₁)
                                                     (weak b a c Rba)) x)
                  (isSymSymClosure R)

Poset→Preorder : Poset ℓ ℓ' → Preorder ℓ ℓ'
Poset→Preorder (_ , pos) = _ , preorderstr (PosetStr._≤_ pos)
                                           (isPoset→IsPreorder (PosetStr.isPoset pos))

Toset→Poset : Toset ℓ ℓ' → Poset ℓ ℓ'
Toset→Poset (_ , tos) = _ , posetstr (TosetStr._≤_ tos)
                                     (isToset→IsPoset (TosetStr.isToset tos))

Loset→StrictPoset : Loset ℓ ℓ' → StrictPoset ℓ ℓ'
Loset→StrictPoset (_ , los)
  = _ , strictposetstr (LosetStr._<_ los)
                       (isLoset→IsStrictPoset (LosetStr.isLoset los))

Poset→StrictPoset : Poset ℓ ℓ' → StrictPoset ℓ (ℓ-max ℓ ℓ')
Poset→StrictPoset (_ , pos)
  = _ , strictposetstr (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
                       (isPoset→IsStrictPosetIrreflKernel (PosetStr.isPoset pos))

Toset→Loset : (tos : Toset ℓ ℓ') → Discrete (fst tos) → Loset ℓ (ℓ-max ℓ ℓ')
Toset→Loset (_ , tos) disc
  = _ , losetstr (BinaryRelation.IrreflKernel (TosetStr._≤_ tos))
                       (isToset→IsLosetIrreflKernel disc
                                                    (TosetStr.isToset tos))

StrictPoset→Poset : StrictPoset ℓ ℓ' → Poset ℓ (ℓ-max ℓ ℓ')
StrictPoset→Poset (_ , strictpos)
  = _ , posetstr (BinaryRelation.ReflClosure (StrictPosetStr._<_ strictpos))
                 (isStrictPoset→IsPosetReflClosure (StrictPosetStr.isStrictPoset strictpos))

Loset→Toset : (los : Loset ℓ ℓ')
            → Discrete (fst los)
            → Toset ℓ (ℓ-max ℓ ℓ')
Loset→Toset (_ , los) disc
  = _ , tosetstr (BinaryRelation.ReflClosure (LosetStr._<_ los))
                 (isLoset→IsTosetReflClosure disc
                                             (LosetStr.isLoset los))

Preorder→StrictPoset : Preorder ℓ ℓ' → StrictPoset ℓ ℓ'
Preorder→StrictPoset (_ , pre)
  = _ , strictposetstr (BinaryRelation.AsymKernel (PreorderStr._≲_ pre))
                       (isPreorder→IsStrictPosetAsymKernel (PreorderStr.isPreorder pre))

StrictPoset→Apartness : (R : StrictPoset ℓ ℓ')
                      → BinaryRelation.isWeaklyLinear (StrictPosetStr._<_ (snd R))
                      → Apartness ℓ ℓ'
StrictPoset→Apartness (_ , strictpos) weak
  = _ , apartnessstr (BinaryRelation.SymClosure (StrictPosetStr._<_ strictpos))
                     (isStrictPoset→IsApartnessSymClosure
                       (StrictPosetStr.isStrictPoset strictpos) weak)

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsPreorder _≲_)
  where

  module _
    (P : Embedding A ℓ'')
    where

    private
      subtype : Type ℓ''
      subtype = fst P

      toA : subtype → A
      toA = fst (snd P)

      prop : ∀ a b → isProp (a ≲ b)
      prop = IsPreorder.is-prop-valued pre

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

    isGreatest : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isGreatest n = (x : subtype) → toA x ≲ toA n

    isPropIsGreatest : ∀ n → isProp (isGreatest n)
    isPropIsGreatest n = isPropΠ λ x → prop (toA x) (toA n)

    isLowerBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isLowerBound n = (x : subtype) → n ≲ toA x

    isPropIsLowerBound : ∀ n → isProp (isLowerBound n)
    isPropIsLowerBound n = isPropΠ λ x → prop n (toA x)

    LowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    LowerBound = Σ[ n ∈ A ] isLowerBound n

    isUpperBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isUpperBound n = (x : subtype) → toA x ≲ n

    isPropIsUpperBound : ∀ n → isProp (isUpperBound n)
    isPropIsUpperBound n = isPropΠ λ x → prop (toA x) n

    UpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    UpperBound = Σ[ n ∈ A ] isUpperBound n

  module _
    (P : Embedding A ℓ'')
    where

    isMaximalLowerBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMaximalLowerBound n
      = Σ[ islb ∈ isLowerBound P n ]
        isMaximal (LowerBound P
                  , EmbeddingΣProp (isPropIsLowerBound P)) (n , islb)

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

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsPreorder _≲_)
  {P : Embedding A ℓ''}
  where

  private
    toA : (fst P) → A
    toA = fst (snd P)

  isLeast→isMinimal : ∀ n → isLeast pre P n → isMinimal pre P n
  isLeast→isMinimal _ isl x _ = isl x

  isGreatest→isMaximal : ∀ n → isGreatest pre P n → isMaximal pre P n
  isGreatest→isMaximal _ isg x _ = isg x

  isLeast→isLowerBound : ∀ n → isLeast pre P n → isLowerBound pre P (toA n)
  isLeast→isLowerBound _ isl = isl

  isGreatest→isUpperBound : ∀ n → isGreatest pre P n → isUpperBound pre P (toA n)
  isGreatest→isUpperBound _ isg = isg

  isLeast→isInfimum : ∀ n → isLeast pre P n → isInfimum pre P (toA n)
  isLeast→isInfimum n isl = (isLeast→isLowerBound n isl) , (λ x → snd x n)

  isGreatest→isSupremum : ∀ n → isGreatest pre P n → isSupremum pre P (toA n)
  isGreatest→isSupremum n isg = (isGreatest→isUpperBound n isg) , (λ x → snd x n)

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
    pre = isPoset→IsPreorder pos

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
    pre = isPoset→IsPreorder (isToset→IsPoset tos)

    toA : (fst P) → A
    toA = fst (snd P)

  isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
  isMinimal→isLeast n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (conn (toA n) (toA m))

  isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
  isMaximal→isGreatest n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (conn (toA n) (toA m))
