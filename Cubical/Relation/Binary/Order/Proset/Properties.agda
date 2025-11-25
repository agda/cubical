module Cubical.Relation.Binary.Order.Proset.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Proset.Base
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

  isProset→isEquivRelSymKernel : IsProset R → isEquivRel (SymKernel R)
  isProset→isEquivRelSymKernel proset
    = equivRel (λ a → (IsProset.is-refl proset a)
                    , (IsProset.is-refl proset a))
               (isSymSymKernel R)
               (λ a b c (Rab , Rba) (Rbc , Rcb)
                 → IsProset.is-trans proset a b c Rab Rbc
                 , IsProset.is-trans proset c b a Rcb Rba)

  isProset→isQuosetAsymKernel : IsProset R → IsQuoset (AsymKernel R)
  isProset→isQuosetAsymKernel proset
    = isquoset (IsProset.is-set proset)
                    (λ a b → isProp× (IsProset.is-prop-valued proset a b) (isProp¬ (R b a)))
                    (λ a (Raa , ¬Raa) → ¬Raa (IsProset.is-refl proset a))
                    (λ a b c (Rab , ¬Rba) (Rbc , ¬Rcb)
                      → IsProset.is-trans proset a b c Rab Rbc
                      , λ Rca → ¬Rcb (IsProset.is-trans proset c a b Rca Rab))
                    (isAsymAsymKernel R)

  isProsetInduced : IsProset R → (B : Type ℓ'') → (f : B ↪ A) → IsProset (InducedRelation R (B , f))
  isProsetInduced pre B (f , emb)
    = isproset (Embedding-into-isSet→isSet (f , emb) (IsProset.is-set pre))
                 (λ a b → IsProset.is-prop-valued pre (f a) (f b))
                 (λ a → IsProset.is-refl pre (f a))
                 λ a b c → IsProset.is-trans pre (f a) (f b) (f c)

  isProsetDual : IsProset R → IsProset (Dual R)
  isProsetDual pre
    = isproset (IsProset.is-set pre)
               (λ a b → IsProset.is-prop-valued pre b a)
               (IsProset.is-refl pre) (λ a b c Rab Rbc → IsProset.is-trans pre c b a Rbc Rab)

Proset→Quoset : Proset ℓ ℓ' → Quoset ℓ ℓ'
Proset→Quoset (_ , pre)
  = quoset _ (BinaryRelation.AsymKernel (ProsetStr._≲_ pre))
             (isProset→isQuosetAsymKernel (ProsetStr.isProset pre))

DualProset : Proset ℓ ℓ' → Proset ℓ ℓ'
DualProset (_ , pre)
  = proset _ (BinaryRelation.Dual (ProsetStr._≲_ pre))
             (isProsetDual (ProsetStr.isProset pre))

module _
  {A : Type ℓ}
  {_≲_ : Rel A A ℓ'}
  (pre : IsProset _≲_)
  where

  private
      prop = IsProset.is-prop-valued pre

      rfl = IsProset.is-refl pre

      trans = IsProset.is-trans pre

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

  isUpperBoundOfSelf→isGreatestOfSelf : ∀{n} → isUpperBound {B = A} (λ x → x) n
                                      → isGreatest (A , (id↪ A)) n
  isUpperBoundOfSelf→isGreatestOfSelf ub = ub

  isLowerBoundOfSelf→isLeastOfSelf : ∀{n} → isLowerBound {B = A} (λ x → x) n
                                   → isLeast (A , (id↪ A)) n
  isLowerBoundOfSelf→isLeastOfSelf lb = lb

  isInfimumOfUpperBounds→isUpperBound : {B : Type ℓ''}
                                      → (P : B → A)
                                      → ∀ n
                                      → isInfimum {B = UpperBound P} fst n
                                      → isUpperBound P n
  isInfimumOfUpperBounds→isUpperBound P _ (_ , gt) x = gt ((P x) , λ { (_ , upy) → upy x })

  isInfimumOfUpperBounds→isSupremum : {B : Type ℓ''}
                                    → (P : B → A)
                                    → ∀ n
                                    → isInfimum {B = UpperBound P} fst n
                                    → isSupremum P n
  isInfimumOfUpperBounds→isSupremum P n (lt , gt)
    = isInfimumOfUpperBounds→isUpperBound P n (lt , gt) , lt

  isSupremumOfLowerBounds→isLowerBound : {B : Type ℓ''}
                                       → (P : B → A)
                                       → ∀ n
                                       → isSupremum {B = LowerBound P} fst n
                                       → isLowerBound P n
  isSupremumOfLowerBounds→isLowerBound P _ (_ , ls) x = ls ((P x) , λ { (_ , lwy) → lwy x })

  isSupremumOfLowerBounds→isInfimum : {B : Type ℓ''}
                                    → (P : B → A)
                                    → ∀ n
                                    → isSupremum {B = LowerBound P} fst n
                                    → isInfimum P n
  isSupremumOfLowerBounds→isInfimum P n (gs , ls)
    = isSupremumOfLowerBounds→isLowerBound P n (gs , ls) , gs

  isMeet : A → A → A → Type (ℓ-max ℓ ℓ')
  isMeet a b a∧b = ∀ x → x ≲ a∧b ≃ (x ≲ a × x ≲ b)

  isJoin : A → A → A → Type (ℓ-max ℓ ℓ')
  isJoin a b a∨b = ∀ x → a∨b ≲ x ≃ (a ≲ x × b ≲ x)

  Meet : ∀ a b → Type (ℓ-max ℓ ℓ')
  Meet a b = Σ[ a∧b ∈ A ] isMeet a b a∧b

  Join : ∀ a b → Type (ℓ-max ℓ ℓ')
  Join a b = Σ[ a∨b ∈ A ] isJoin a b a∨b

  isPropIsMeet : ∀ a b a∧b → isProp (isMeet a b a∧b)
  isPropIsMeet a b c = isPropΠ λ x → isOfHLevel≃ 1 (prop x c)
                                                    (isProp× (prop x a)
                                                             (prop x b))

  isPropIsJoin : ∀ a b a∨b → isProp (isJoin a b a∨b)
  isPropIsJoin a b c = isPropΠ λ x → isOfHLevel≃ 1 (prop c x)
                                                    (isProp× (prop a x)
                                                             (prop b x))

  isReflIsMeet : ∀ a → isMeet a a a
  isReflIsMeet a x = propBiimpl→Equiv (prop x a)
                                      (isProp× (prop x a) (prop x a))
                                      (λ a → a , a)
                                       fst

  isReflIsJoin : ∀ a → isJoin a a a
  isReflIsJoin a x = propBiimpl→Equiv (prop a x)
                                      (isProp× (prop a x) (prop a x))
                                      (λ a → a , a)
                                       fst

  isMeet≃isInfimum : ∀ a b c
                   → isMeet a b c
                   ≃ isInfimum {B = Σ[ x ∈ A ] (x ≡ a) ⊎ (x ≡ b)} fst c
  isMeet≃isInfimum a b a∧b
    = propBiimpl→Equiv (isPropIsMeet a b a∧b) (isPropIsInfimum fst a∧b)
                       (λ fun → ⊎.rec (λ x≡a → subst
                                               (a∧b ≲_)
                                               (sym x≡a)
                                               (fun a∧b .fst (rfl a∧b) .fst))
                                      (λ x≡b → subst
                                               (a∧b ≲_)
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
                                               (x ≲_)
                                               (sym y≡a)
                                                x≤a)
                                      (λ y≡b → subst
                                               (x ≲_)
                                               (sym y≡b)
                                                x≤b)
                                       ∘ snd)) } }

  isJoin≃isSupremum : ∀ a b c
                    → isJoin a b c
                    ≃ isSupremum {B = Σ[ x ∈ A ] (x ≡ a) ⊎ (x ≡ b)} fst c
  isJoin≃isSupremum a b a∨b
    = propBiimpl→Equiv (isPropIsJoin a b a∨b) (isPropIsSupremum fst a∨b)
                       (λ fun → ⊎.rec (λ x≡a → subst
                                               (_≲ a∨b)
                                               (sym x≡a)
                                               (fun a∨b .fst (rfl a∨b) .fst))
                                      (λ x≡b → subst
                                               (_≲ a∨b)
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
                                               (_≲ x)
                                               (sym y≡a)
                                                a≤x)
                                      (λ y≡b → subst
                                               (_≲ x)
                                               (sym y≡b)
                                                b≤x)
                                ∘ snd)) } }

  isMeetComm : ∀ a b a∧b → isMeet a b a∧b → isMeet b a a∧b
  isMeetComm _ _ _ fun x = compEquiv (fun x) Σ-swap-≃

  isJoinComm : ∀ a b a∨b → isJoin a b a∨b → isJoin b a a∨b
  isJoinComm _ _ _ fun x = compEquiv (fun x) Σ-swap-≃

  isMeetAssoc : ∀ a b c a∧b b∧c a∧b∧c
              → isMeet a b a∧b
              → isMeet b c b∧c
              → isMeet a b∧c a∧b∧c
              → isMeet a∧b c a∧b∧c
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
              → isJoin a b a∨b
              → isJoin b c b∨c
              → isJoin a b∨c a∨b∨c
              → isJoin a∨b c a∨b∨c
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

  isMeetIsotone : ∀ a b c d a∧c b∧d
                → isMeet a c a∧c
                → isMeet b d b∧d
                → a ≲ b
                → c ≲ d
                → a∧c ≲ b∧d
  isMeetIsotone a b c d a∧c b∧d meeta∧c meetb∧d a≲b c≲d
    = invEq (meetb∧d a∧c) (trans a∧c a b a∧c≲a a≲b , trans a∧c c d a∧c≲c c≲d)
      where a∧c≲a = equivFun (meeta∧c a∧c) (rfl a∧c) .fst
            a∧c≲c = equivFun (meeta∧c a∧c) (rfl a∧c) .snd

  isJoinIsotone : ∀ a b c d a∨c b∨d
                → isJoin a c a∨c
                → isJoin b d b∨d
                → a ≲ b
                → c ≲ d
                → a∨c ≲ b∨d
  isJoinIsotone a b c d a∨c b∨d joina∨c joinb∨d a≲b c≲d
    = invEq (joina∨c b∨d) (trans a b b∨d a≲b b≲b∨d , trans c d b∨d c≲d d≲b∨d)
    where b≲b∨d = equivFun (joinb∨d b∨d) (rfl b∨d) .fst
          d≲b∨d = equivFun (joinb∨d b∨d) (rfl b∨d) .snd
