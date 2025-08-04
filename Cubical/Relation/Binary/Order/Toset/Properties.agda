module Cubical.Relation.Binary.Order.Toset.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Proset.Properties
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset.Base
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

  isToset→isPoset : IsToset R → IsPoset R
  isToset→isPoset toset = isposet
                          (IsToset.is-set toset)
                          (IsToset.is-prop-valued toset)
                          (IsToset.is-refl toset)
                          (IsToset.is-trans toset)
                          (IsToset.is-antisym toset)

  isTosetDecidable→Discrete : IsToset R → isDecidable R → Discrete A
  isTosetDecidable→Discrete = isPosetDecidable→Discrete ∘ isToset→isPoset

  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isToset→isLosetIrreflKernel : IsToset R → isDecidable R → IsLoset (IrreflKernel R)
  isToset→isLosetIrreflKernel toset dec
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
                                  (IsToset.is-total toset b c))
                         (λ ¬a≡b → ∥₁.map (⊎.map (λ Rab → Rab , ¬a≡b)
                                   (λ Rba → (IsToset.is-trans toset b a c Rba Rac)
                                   , λ b≡c → ¬a≡b (IsToset.is-antisym toset a b
                                       (subst (λ x → R a x) (sym b≡c) Rac) Rba)))
                                 (IsToset.is-total toset a b))
                         (disc a b))
               λ { a b (¬¬Rab , ¬¬Rba) → IsToset.is-antisym toset a b
                                         (decRec (λ Rab → Rab)
                                           (λ ¬Rab → ⊥.rec (∥₁.rec isProp⊥
                                             (⊎.rec ¬Rab λ Rba → ¬¬Rba (Rba ,
                                               (λ b≡a → ¬Rab (subst (λ x → R x b) b≡a
                                                 (IsToset.is-refl toset b)))))
                                             (IsToset.is-total toset a b))) (dec a b))
                                         (decRec (λ Rba → Rba)
                                           (λ ¬Rba → ⊥.rec (∥₁.rec isProp⊥
                                             (⊎.rec ¬Rba λ Rab → ¬¬Rab (Rab ,
                                               (λ a≡b → ¬Rba (subst (λ x → R x a) a≡b
                                                 (IsToset.is-refl toset a)))))
                                             (IsToset.is-total toset b a))) (dec b a))}
    where disc : Discrete A
          disc = isTosetDecidable→Discrete toset dec

  isTosetDecidable→isLosetDecidable : IsToset R → isDecidable R → isDecidable (IrreflKernel R)
  isTosetDecidable→isLosetDecidable tos dec a b with dec a b
  ... | no ¬Rab = no λ { (Rab , _) → ¬Rab Rab }
  ... | yes Rab with (isTosetDecidable→Discrete tos dec) a b
  ...       | yes a≡b = no λ { (_ , ¬a≡b) → ¬a≡b a≡b }
  ...       | no  a≢b = yes (Rab , a≢b)

  isTosetInduced : IsToset R → (B : Type ℓ'') → (f : B ↪ A)
                 → IsToset (InducedRelation R (B , f))
  isTosetInduced tos B (f , emb)
    = istoset (Embedding-into-isSet→isSet (f , emb) (IsToset.is-set tos))
              (λ a b → IsToset.is-prop-valued tos (f a) (f b))
              (λ a → IsToset.is-refl tos (f a))
              (λ a b c → IsToset.is-trans tos (f a) (f b) (f c))
              (λ a b a≤b b≤a → isEmbedding→Inj emb a b
                (IsToset.is-antisym tos (f a) (f b) a≤b b≤a))
              λ a b → IsToset.is-total tos (f a) (f b)

  isTosetDual : IsToset R → IsToset (Dual R)
  isTosetDual tos
    = istoset (IsToset.is-set tos)
              (λ a b → IsToset.is-prop-valued tos b a)
              (IsToset.is-refl tos)
              (λ a b c Rab Rbc → IsToset.is-trans tos c b a Rbc Rab)
              (λ a b Rab Rba → IsToset.is-antisym tos a b Rba Rab)
               λ a b → IsToset.is-total tos b a

Toset→Poset : Toset ℓ ℓ' → Poset ℓ ℓ'
Toset→Poset (_ , tos)
  = poset _ (TosetStr._≤_ tos)
            (isToset→isPoset (TosetStr.isToset tos))

Toset→Loset : (tos : Toset ℓ ℓ')
            → BinaryRelation.isDecidable (TosetStr._≤_ (snd tos))
            → Loset ℓ (ℓ-max ℓ ℓ')
Toset→Loset (_ , tos) dec
  = loset _ (BinaryRelation.IrreflKernel (TosetStr._≤_ tos))
            (isToset→isLosetIrreflKernel (TosetStr.isToset tos) dec)

DualToset : Toset ℓ ℓ' → Toset ℓ ℓ'
DualToset (_ , tos)
  = toset _ (BinaryRelation.Dual (TosetStr._≤_ tos))
            (isTosetDual (TosetStr.isToset tos))

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (tos : IsToset _≤_)
  where

  private
      pos = isToset→isPoset tos

      pre = isPoset→isProset pos

      prop = IsToset.is-prop-valued tos

      rfl = IsToset.is-refl tos

      anti = IsToset.is-antisym tos

      trans = IsToset.is-trans tos

      total = IsToset.is-total tos

  module _
    {P : Embedding A ℓ''}
    where

    private
      toA = fst (snd P)

    isMinimal→isLeast : ∀ n → isMinimal pre P n → isLeast pre P n
    isMinimal→isLeast n ism m
      = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → n≤m) (λ m≤n → ism m m≤n)) (total (toA n) (toA m))

    isMaximal→isGreatest : ∀ n → isMaximal pre P n → isGreatest pre P n
    isMaximal→isGreatest n ism m
      = ∥₁.rec (prop _ _) (⊎.rec (λ n≤m → ism m n≤m) (λ m≤n → m≤n)) (total (toA n) (toA m))

TosetIsPseudolattice : (tos : Toset ℓ ℓ')
                     → isPseudolattice (Toset→Poset tos)
TosetIsPseudolattice tos = meet , join
  where
    is = TosetStr.isToset (tos .snd)

    posis = PosetStr.isPoset (Toset→Poset tos .snd)

    prop = IsToset.is-prop-valued is

    rfl = IsToset.is-refl is

    trans = IsToset.is-trans is

    total = IsToset.is-total is

    meet : isMeetSemipseudolattice (Toset→Poset tos)
    meet a b = ∥₁.rec (MeetUnique posis a b)
                 (⊎.rec
                   (λ a≤b → a ,
                     λ x → propBiimpl→Equiv
                             (prop _ _)
                             (isProp× (prop _ _) (prop _ _))
                             (λ x≤a → x≤a , (trans x a b x≤a a≤b))
                              fst)
                   (λ b≤a → b ,
                     λ x → propBiimpl→Equiv
                             (prop _ _)
                             (isProp× (prop _ _) (prop _ _))
                             (λ x≤b → trans x b a x≤b b≤a , x≤b)
                              snd))
                 (total a b)

    join : isJoinSemipseudolattice (Toset→Poset tos)
    join a b = ∥₁.rec (JoinUnique posis a b)
                 (⊎.rec
                   (λ a≤b → b ,
                     λ x → propBiimpl→Equiv
                             (prop _ _)
                             (isProp× (prop _ _) (prop _ _))
                             (λ b≤x → trans a b x a≤b b≤x , b≤x)
                              snd)
                   (λ b≤a → a ,
                     λ x → propBiimpl→Equiv
                             (prop _ _)
                             (isProp× (prop _ _) (prop _ _))
                             (λ a≤x → a≤x , trans b a x b≤a a≤x)
                              fst))
                 (total a b)

-- We take the pseudolattice component in as an assumption because more likely than not,
-- the goal is to prove some meet and join on a toset is distributive, not the
-- meet and join that implicitly come with any toset
TosetIsDistributivePseudolattice : (tos : Toset ℓ ℓ')
                                 → (lat : isPseudolattice (Toset→Poset tos))
                                 → MeetDistLJoin (Toset→Poset tos) lat
TosetIsDistributivePseudolattice tos lat = dist
  where
    _≤_ = TosetStr._≤_ (tos .snd)
    is = TosetStr.isToset (tos .snd)

    pos = isToset→isPoset is

    pro = isPoset→isProset pos

    set = IsToset.is-set is

    rfl = IsToset.is-refl is

    trans = IsToset.is-trans is

    anti = IsToset.is-antisym is

    total = IsToset.is-total is

    _∧l_ : ⟨ tos ⟩ → ⟨ tos ⟩ → ⟨ tos ⟩
    a ∧l b = lat .fst a b .fst

    meet : ∀ a b → isMeet pro a b (a ∧l b)
    meet a b = lat .fst a b .snd

    _∨l_ : ⟨ tos ⟩ → ⟨ tos ⟩ → ⟨ tos ⟩
    a ∨l b = lat .snd a b .fst

    join : ∀ a b → isJoin pro a b (a ∨l b)
    join a b = lat .snd a b .snd

    order→meet : ∀{a b} → a ≤ b → a ∧l b ≡ a
    order→meet {a} {b} a≤b = sym (equivFun (order≃meet pos a b (a ∧l b) (meet a b)) a≤b)

    order→join : ∀{a b} → a ≤ b → a ∨l b ≡ b
    order→join {a} {b} a≤b = sym (equivFun (order≃join pos a b (a ∨l b) (join a b)) a≤b)

    ∧Comm : ∀{a b} → a ∧l b ≡ b ∧l a
    ∧Comm {a} {b} = meetComm pos (λ x y → (x ∧l y) , meet x y) a b

    ∨Comm : ∀{ a b } → a ∨l b ≡ b ∨l a
    ∨Comm {a} {b} = joinComm pos (λ x y → (x ∨l y) , join x y) a b

    dist : ∀ a b c
         → a ∧l (b ∨l c) ≡ (a ∧l b) ∨l (a ∧l c)
    dist a b c = lem1+2+3+4+5+6+7+8
      where
        goal = a ∧l (b ∨l c) ≡ (a ∧l b) ∨l (a ∧l c)

        lem1 : a ≤ b
             → b ≤ c
             → a ≤ c
             → goal
        lem1 a≤b b≤c a≤c = (cong (a ∧l_) (order→join b≤c) ∙
                                   order→meet a≤c) ∙
                             sym (cong₂ _∨l_ (order→meet a≤b)
                                             (order→meet a≤c) ∙
                                  order→join (rfl a))

        lem2 : a ≤ b
             → b ≤ c
             → c ≤ a
             → goal
        lem2 a≤b b≤c c≤a = (cong (a ∧l_) (order→join b≤c) ∙
                                   ∧Comm ∙
                                   order→meet c≤a) ∙
                             sym (cong₂ _∨l_ (order→meet a≤b)
                                             (∧Comm ∙ order→meet c≤a) ∙
                                  ∨Comm ∙
                                  order→join c≤a ∙
                                  anti a c (trans a b c a≤b b≤c) c≤a)

        lem1+2 : a ≤ b
               → b ≤ c
               → goal
        lem1+2 a≤b b≤c = ∥₁.rec (set _ _) (⊎.rec (lem1 a≤b b≤c) (lem2 a≤b b≤c)) (total a c)

        lem3 : a ≤ b
             → c ≤ b
             → a ≤ c
             → goal
        lem3 a≤b c≤b a≤c = (cong (a ∧l_) (∨Comm ∙
                                            order→join c≤b) ∙
                                    order→meet a≤b) ∙
                             sym (cong₂ _∨l_ (order→meet a≤b)
                                             (order→meet a≤c) ∙
                                  order→join (rfl a))

        lem4 : a ≤ b
             → c ≤ b
             → c ≤ a
             → goal
        lem4 a≤b c≤b c≤a = (cong (a ∧l_) (∨Comm ∙
                                            order→join c≤b) ∙
                                    order→meet a≤b) ∙
                             sym (cong₂ _∨l_ (order→meet a≤b)
                                             (∧Comm ∙ order→meet c≤a) ∙
                                  ∨Comm ∙
                                  order→join c≤a)

        lem3+4 : a ≤ b
               → c ≤ b
               → goal
        lem3+4 a≤b c≤b = ∥₁.rec (set _ _ ) (⊎.rec (lem3 a≤b c≤b) (lem4 a≤b c≤b)) (total a c)

        lem1+2+3+4 : a ≤ b
                   → goal
        lem1+2+3+4 a≤b = ∥₁.rec (set _ _) (⊎.rec (lem1+2 a≤b) (lem3+4 a≤b)) (total b c)

        lem5 : b ≤ a
             → b ≤ c
             → a ≤ c
             → goal
        lem5 b≤a b≤c a≤c = (cong (a ∧l_) (order→join b≤c) ∙
                                   order→meet a≤c) ∙
                             sym (cong₂ _∨l_ (∧Comm ∙ order→meet b≤a) (order→meet a≤c) ∙
                                  order→join b≤a)

        lem6 : b ≤ a
             → b ≤ c
             → c ≤ a
             → goal
        lem6 b≤a b≤c c≤a = (cong (a ∧l_) (order→join b≤c) ∙
                                   ∧Comm ∙
                                   order→meet c≤a) ∙
                             sym (cong₂ _∨l_ (∧Comm ∙ order→meet b≤a)
                                             (∧Comm ∙ order→meet c≤a) ∙
                                  order→join b≤c)

        lem5+6 : b ≤ a
               → b ≤ c
               → goal
        lem5+6 b≤a b≤c = ∥₁.rec (set _ _) (⊎.rec (lem5 b≤a b≤c) (lem6 b≤a b≤c)) (total a c)

        lem7 : b ≤ a
             → c ≤ b
             → a ≤ c
             → goal
        lem7 b≤a c≤b a≤c = (cong (a ∧l_) (∨Comm ∙ order→join c≤b) ∙
                                   ∧Comm ∙
                                   order→meet b≤a) ∙
                             sym (cong₂ _∨l_ (∧Comm ∙ order→meet b≤a)
                                             (order→meet a≤c) ∙
                                  order→join b≤a ∙ anti a b (trans a c b a≤c c≤b) b≤a)

        lem8 : b ≤ a
             → c ≤ b
             → c ≤ a
             → goal
        lem8 b≤a c≤b c≤a = (cong (a ∧l_) (∨Comm ∙ order→join c≤b) ∙
                                   ∧Comm ∙
                                   order→meet b≤a) ∙
                             sym (cong₂ _∨l_ (∧Comm ∙ order→meet b≤a)
                                             (∧Comm ∙ order→meet c≤a) ∙
                                  ∨Comm ∙ order→join c≤b)

        lem7+8 : b ≤ a
               → c ≤ b
               → goal
        lem7+8 b≤a c≤b = ∥₁.rec (set _ _) (⊎.rec (lem7 b≤a c≤b) (lem8 b≤a c≤b)) (total a c)

        lem5+6+7+8 : b ≤ a
                   → goal
        lem5+6+7+8 b≤a = ∥₁.rec (set _ _) (⊎.rec (lem5+6 b≤a) (lem7+8 b≤a)) (total b c)

        lem1+2+3+4+5+6+7+8 : goal
        lem1+2+3+4+5+6+7+8 = ∥₁.rec (set _ _) (⊎.rec lem1+2+3+4 lem5+6+7+8) (total a b)
