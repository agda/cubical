{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Properties where

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.Empty.Base as ⊥

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Loset
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.StrictPoset
open import Cubical.Relation.Binary.Order.StrictLoset

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→isPreorder : IsPoset R → IsPreorder R
  isPoset→isPreorder poset = ispreorder
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  isLoset→isPoset : IsLoset R → IsPoset R
  isLoset→isPoset loset = isposet
                          (IsLoset.is-set loset)
                          (IsLoset.is-prop-valued loset)
                          (IsLoset.is-refl loset)
                          (IsLoset.is-trans loset)
                          (IsLoset.is-antisym loset)

  isStrictLoset→isStrictPoset : IsStrictLoset R → IsStrictPoset R
  isStrictLoset→isStrictPoset sloset = isstrictposet
                                       (IsStrictLoset.is-set sloset)
                                       (IsStrictLoset.is-prop-valued sloset)
                                       (IsStrictLoset.is-irrefl sloset)
                                       (IsStrictLoset.is-trans sloset)
                                       (IsStrictLoset.is-asym sloset)

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

  isPoset→isStrictPosetIrreflKernel : IsPoset R → IsStrictPoset (IrreflKernel R)
  isPoset→isStrictPosetIrreflKernel poset
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

  isLoset→isStrictLosetIrreflKernel : IsLoset R → IsStrictLoset (IrreflKernel R)
  isLoset→isStrictLosetIrreflKernel loset
    = isstrictloset (IsLoset.is-set loset)
                    (λ a b → isProp× (IsLoset.is-prop-valued loset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsLoset.is-trans loset)
                                 (IsLoset.is-antisym loset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsLoset.is-trans loset)
                                                           (IsLoset.is-antisym loset)))
                    (isConnectedStronglyConnectedIrreflKernel R
                      (IsLoset.is-strongly-connected loset))

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

  isStrictLoset→isLosetReflClosure : Discrete A → IsStrictLoset R → IsLoset (ReflClosure R)
  isStrictLoset→isLosetReflClosure disc strictloset
    = isloset (IsStrictLoset.is-set strictloset)
              (λ a b → isProp⊎ (IsStrictLoset.is-prop-valued strictloset a b)
                               (IsStrictLoset.is-set strictloset a b)
                               λ Rab a≡b
                                 → IsStrictLoset.is-irrefl strictloset a (subst (R a)
                                                                         (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsStrictLoset.is-trans strictloset))
              (antisym (IsStrictLoset.is-irrefl strictloset)
                       (IsStrictLoset.is-trans strictloset))
              λ a b → decRec (λ a≡b → ∣ inl (inr a≡b) ∣₁)
                             (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → inl Rab) λ Rba → inl Rba)
                             (IsStrictLoset.is-connected strictloset a b ¬a≡b)) (disc a b)

  isPreorder→isEquivRelSymKernel : IsPreorder R → isEquivRel (SymKernel R)
  isPreorder→isEquivRelSymKernel preorder
    = equivRel (λ a → (IsPreorder.is-refl preorder a)
                    , (IsPreorder.is-refl preorder a))
               (isSymSymKernel R)
               (λ a b c (Rab , Rba) (Rbc , Rcb)
                 → IsPreorder.is-trans preorder a b c Rab Rbc
                 , IsPreorder.is-trans preorder c b a Rcb Rba)

  isPreorder→isStrictPosetAsymKernel : IsPreorder R → IsStrictPoset (AsymKernel R)
  isPreorder→isStrictPosetAsymKernel preorder
    = isstrictposet (IsPreorder.is-set preorder)
                    (λ a b → isProp× (IsPreorder.is-prop-valued preorder a b) (isProp¬ (R b a)))
                    (λ a (Raa , ¬Raa) → ¬Raa (IsPreorder.is-refl preorder a))
                    (λ a b c (Rab , ¬Rba) (Rbc , ¬Rcb)
                      → IsPreorder.is-trans preorder a b c Rab Rbc
                      , λ Rca → ¬Rcb (IsPreorder.is-trans preorder c a b Rca Rab))
                    (isAsymAsymKernel R)

  isStrictPoset→isApartnessSymClosure : IsStrictPoset R → isWeaklyLinear R → IsApartness (SymClosure R)
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
                                     (λ Rba → ∥₁.rec squash₁ (λ y → ∣ ⊎.rec (λ Rbc → inr (inl Rbc))
                                                                            (λ Rca → inl (inr Rca)) y ∣₁)
                                                                     (weak b a c Rba)) x)
                  (isSymSymClosure R)

Poset→Preorder : Poset ℓ ℓ' → Preorder ℓ ℓ'
Poset→Preorder (_ , pos) = _ , preorderstr (PosetStr._≤_ pos)
                                           (isPoset→isPreorder (PosetStr.isPoset pos))

Loset→Poset : Loset ℓ ℓ' → Poset ℓ ℓ'
Loset→Poset (_ , los) = _ , posetstr (LosetStr._≤_ los)
                                     (isLoset→isPoset (LosetStr.isLoset los))

StrictLoset→StrictPoset : StrictLoset ℓ ℓ' → StrictPoset ℓ ℓ'
StrictLoset→StrictPoset (_ , strictlos)
  = _ , strictposetstr (StrictLosetStr._<_ strictlos)
                       (isStrictLoset→isStrictPoset (StrictLosetStr.isStrictLoset strictlos))

Poset→StrictPoset : Poset ℓ ℓ' → StrictPoset ℓ (ℓ-max ℓ ℓ')
Poset→StrictPoset (_ , pos)
  = _ , strictposetstr (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
                       (isPoset→isStrictPosetIrreflKernel (PosetStr.isPoset pos))

Loset→StrictLoset : Loset ℓ ℓ' → StrictLoset ℓ (ℓ-max ℓ ℓ')
Loset→StrictLoset (_ , los)
  = _ , strictlosetstr (BinaryRelation.IrreflKernel (LosetStr._≤_ los))
                       (isLoset→isStrictLosetIrreflKernel (LosetStr.isLoset los))

StrictPoset→Poset : StrictPoset ℓ ℓ' → Poset ℓ (ℓ-max ℓ ℓ')
StrictPoset→Poset (_ , strictpos)
  = _ , posetstr (BinaryRelation.ReflClosure (StrictPosetStr._<_ strictpos))
                 (isStrictPoset→isPosetReflClosure (StrictPosetStr.isStrictPoset strictpos))

StrictLoset→Loset : (strictlos : StrictLoset ℓ ℓ')
                  → Discrete (fst strictlos)
                  → Loset ℓ (ℓ-max ℓ ℓ')
StrictLoset→Loset (_ , strictlos) disc
  = _ , losetstr (BinaryRelation.ReflClosure (StrictLosetStr._<_ strictlos))
                 (isStrictLoset→isLosetReflClosure disc
                                                   (StrictLosetStr.isStrictLoset strictlos))

Preorder→StrictPoset : Preorder ℓ ℓ' → StrictPoset ℓ ℓ'
Preorder→StrictPoset (_ , pre)
  = _ , strictposetstr (BinaryRelation.AsymKernel (PreorderStr._≲_ pre))
                       (isPreorder→isStrictPosetAsymKernel (PreorderStr.isPreorder pre))

StrictPoset→Apartness : (R : StrictPoset ℓ ℓ')
                      → BinaryRelation.isWeaklyLinear (StrictPosetStr._<_ (snd R))
                      → Apartness ℓ ℓ'
StrictPoset→Apartness (_ , strictpos) weak
  = _ , apartnessstr (BinaryRelation.SymClosure (StrictPosetStr._<_ strictpos))
                     (isStrictPoset→isApartnessSymClosure
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

    isPropisMinimal : ∀ n → isProp (isMinimal n)
    isPropisMinimal n = isPropΠ2 λ x _ → prop (toA n) (toA x)

    Minimal : Type (ℓ-max ℓ' ℓ'')
    Minimal = Σ[ n ∈ subtype ] isMinimal n

    isMaximal : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isMaximal n = (x : subtype) → toA n ≲ toA x → toA x ≲ toA n

    isPropisMaximal : ∀ n → isProp (isMaximal n)
    isPropisMaximal n = isPropΠ2 λ x _ → prop (toA x) (toA n)

    Maximal : Type (ℓ-max ℓ' ℓ'')
    Maximal = Σ[ n ∈ subtype ] isMaximal n

    isLeast : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isLeast n = (x : subtype) → toA n ≲ toA x

    isPropisLeast : ∀ n → isProp (isLeast n)
    isPropisLeast n = isPropΠ λ x → prop (toA n) (toA x)

    isGreatest : (n : subtype) → Type (ℓ-max ℓ' ℓ'')
    isGreatest n = (x : subtype) → toA x ≲ toA n

    isPropisGreatest : ∀ n → isProp (isGreatest n)
    isPropisGreatest n = isPropΠ λ x → prop (toA x) (toA n)

    isLowerBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isLowerBound n = (x : subtype) → n ≲ toA x

    isPropisLowerBound : ∀ n → isProp (isLowerBound n)
    isPropisLowerBound n = isPropΠ λ x → prop n (toA x)

    LowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    LowerBound = Σ[ n ∈ A ] isLowerBound n

    isUpperBound : (n : A) → Type (ℓ-max ℓ' ℓ'')
    isUpperBound n = (x : subtype) → toA x ≲ n

    isPropisUpperBound : ∀ n → isProp (isUpperBound n)
    isPropisUpperBound n = isPropΠ λ x → prop (toA x) n

    UpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    UpperBound = Σ[ n ∈ A ] isUpperBound n

  module _
    (P : Embedding A ℓ'')
    where

    isMaximalLowerBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMaximalLowerBound n
      = Σ[ islb ∈ isLowerBound P n ]
        isMaximal (LowerBound P
                  , EmbeddingΣProp (isPropisLowerBound P)) (n , islb)

    isPropisMaximalLowerBound : ∀ n → isProp (isMaximalLowerBound n)
    isPropisMaximalLowerBound n
      = isPropΣ (isPropisLowerBound P n)
                λ islb → isPropisMaximal (LowerBound P
                       , EmbeddingΣProp (isPropisLowerBound P)) (n , islb)

    MaximalLowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    MaximalLowerBound = Σ[ n ∈ A ] isMaximalLowerBound n

    isMinimalUpperBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMinimalUpperBound n
      = Σ[ isub ∈ isUpperBound P n ]
        isMinimal (UpperBound P
                  , EmbeddingΣProp (isPropisUpperBound P)) (n , isub)

    isPropisMinimalUpperBound : ∀ n → isProp (isMinimalUpperBound n)
    isPropisMinimalUpperBound n
      = isPropΣ (isPropisUpperBound P n)
                λ isub → isPropisMinimal (UpperBound P
                       , EmbeddingΣProp (isPropisUpperBound P)) (n , isub)

    MinimalUpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    MinimalUpperBound = Σ[ n ∈ A ] isMinimalUpperBound n

    isInfimum : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isInfimum n
      = Σ[ islb ∈ isLowerBound P n ]
        isGreatest (LowerBound P
                   , EmbeddingΣProp (isPropisLowerBound P)) (n , islb)

    isPropisInfimum : ∀ n → isProp (isInfimum n)
    isPropisInfimum n
      = isPropΣ (isPropisLowerBound P n)
                λ islb → isPropisGreatest (LowerBound P
                       , EmbeddingΣProp (isPropisLowerBound P)) (n , islb)

    isSupremum : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isSupremum n
      = Σ[ isub ∈ isUpperBound P n ]
        isLeast (UpperBound P
                , EmbeddingΣProp (isPropisUpperBound P)) (n , isub)

    isPropisSupremum : ∀ n → isProp (isSupremum n)
    isPropisSupremum n
      = isPropΣ (isPropisUpperBound P n)
                λ isub → isPropisLeast (UpperBound P
                       , EmbeddingΣProp (isPropisUpperBound P)) (n , isub)

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
  isInfimum→isLowerBound _ (isl , _) = isl

  isSupremum→isUpperBound : ∀ n → isSupremum pre P n → isUpperBound pre P n
  isSupremum→isUpperBound _ (isg , _) = isg

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
  (los : IsLoset _≤_)
  where

  private
    prop : ∀ a b → isProp (a ≤ b)
    prop = IsLoset.is-prop-valued los

    conn : BinaryRelation.isStronglyConnected _≤_
    conn = IsLoset.is-strongly-connected los

    pre : IsPreorder _≤_
    pre = isPoset→isPreorder (isLoset→isPoset los)

    toA : (fst P) → A
    toA = fst (snd P)

  isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
  isMinimal→isLeast n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (conn (toA n) (toA m))

  isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
  isMaximal→isGreatest n ism m
    = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (conn (toA n) (toA m))
