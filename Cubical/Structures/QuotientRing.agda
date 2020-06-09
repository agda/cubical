{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.QuotientRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using (_∈_)
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Structures.Ring
open import Cubical.Structures.Ideal

private
  variable
    ℓ : Level

module _ (R′ : Ring {ℓ}) (I : ⟨ R′ ⟩  → hProp ℓ) (I-isIdeal : isIdeal R′ I) where
  private
    open ring-syntax R′
    open isIdeal I-isIdeal
    open ring-axioms R′
    open theory R′
    R = ⟨ R′ ⟩

  R/I : Type ℓ
  R/I = R / (λ x y → x - y ∈ I)

  private
    homogeneity : ∀ (x a b : R)
                 → (a - b ∈ I)
                 → (x + a) - (x + b) ∈ I
    homogeneity x a b p = subst (λ u → u ∈ I) (translatedDifference x a b) p

    isSetR/I : isSet R/I
    isSetR/I = squash/
    [_]/I : (a : R) → R/I
    [ a ]/I = [ a ]

    lemma : (x y a : R)
            → x - y ∈ I
            → [ x + a ]/I ≡ [ y + a ]/I
    lemma x y a x-y∈I = eq/ (x + a) (y + a) (subst (λ u → u ∈ I) calculate x-y∈I)
      where calculate : x - y ≡ (x + a) - (y + a)
            calculate =
                      x - y                 ≡⟨ translatedDifference a x y ⟩
                      ((a + x) - (a + y))   ≡⟨ cong (λ u → u - (a + y)) (ring+-comm _ _) ⟩
                      ((x + a) - (a + y))   ≡⟨ cong (λ u → (x + a) - u) (ring+-comm _ _) ⟩
                      ((x + a) - (y + a))   ∎

    pre-+/I : R → R/I → R/I
    pre-+/I x = elim
                    (λ _ → squash/)
                    (λ y → [ x + y ])
                    λ y y' diffrenceInIdeal
                      → eq/ (x + y) (x + y') (homogeneity x y y' diffrenceInIdeal)

    pre-+/I-DescendsToQuotient : (x y : R) → (x - y ∈ I)
                  → pre-+/I x ≡ pre-+/I y
    pre-+/I-DescendsToQuotient x y x-y∈I i r = pointwise-equal r i
      where
        pointwise-equal : ∀ (u : R/I)
                          → pre-+/I x u ≡ pre-+/I y u
        pointwise-equal = elimProp (λ u → isSetR/I (pre-+/I x u) (pre-+/I y u))
                                   (λ a → lemma x y a x-y∈I)

    _+/I_ : R/I → R/I → R/I
    x +/I y = (elim R/I→R/I-isSet pre-+/I pre-+/I-DescendsToQuotient x) y
      where
        R/I→R/I-isSet : R/I → isSet (R/I → R/I)
        R/I→R/I-isSet _ = isSetΠ (λ _ → squash/)

    +/I-comm : (x y : R/I) → x +/I y ≡ y +/I x
    +/I-comm = elimProp2 (λ _ _ → squash/ _ _) eq
       where eq : (x y : R) → [ x ] +/I [ y ] ≡ [ y ] +/I [ x ]
             eq x y i =  [ ring+-comm x y i ]

    +/I-is-associative : (x y z : R/I) → x +/I (y +/I z) ≡ (x +/I y) +/I z
    +/I-is-associative = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where eq : (x y z : R) → [ x ] +/I ([ y ] +/I [ z ]) ≡ ([ x ] +/I [ y ]) +/I [ z ]
            eq x y z i =  [ ring+-assoc x y z i ]


    0/I : R/I
    0/I = [ 0r ]

    1/I : R/I
    1/I = [ 1r ]

    -/I : R/I → R/I
    -/I = elim (λ _ → squash/) (λ x' → [ - x' ]) eq
      where
        eq : (x y : R) → (x - y ∈ I) → [ - x ] ≡ [ - y ]
        eq x y x-y∈I = eq/ (- x) (- y) (subst (λ u → u ∈ I) eq' (isIdeal.-closed I-isIdeal x-y∈I))
          where
            eq' = - (x + (- y))       ≡⟨ sym (-isDistributive _ _) ⟩
                  (- x) - (- y)       ∎

    +/I-rinv : (x : R/I) → x +/I (-/I x) ≡ 0/I
    +/I-rinv = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I (-/I [ x ]) ≡ 0/I
        eq x i = [ ring+-rinv x i ]


    +/I-rid : (x : R/I) → x +/I 0/I ≡ x
    +/I-rid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I 0/I ≡ [ x ]
        eq x i = [ ring+-rid x i ]

    _·/I_ : R/I → R/I → R/I
    _·/I_ =
      elim (λ _ → isSetΠ (λ _ → squash/))
               (λ x → left· x)
               eq'
      where
        eq : (x y y' : R) → (y - y' ∈ I) → [ x · y ] ≡ [ x · y' ]
        eq x y y' y-y'∈I = eq/ _ _
                             (subst (λ u → u ∈ I)
                                  (x · (y - y')            ≡⟨ ring-rdist _ _ _ ⟩
                                  ((x · y) + x · (- y'))   ≡⟨ cong (λ u → (x · y) + u)
                                                                   (-commutesWithRight-· x y')  ⟩
                                  (x · y) - (x · y')       ∎)
                                  (isIdeal.·-closedLeft I-isIdeal x y-y'∈I))
        left· : (x : R) → R/I → R/I
        left· x = elim (λ y → squash/)
                     (λ y → [ x · y ])
                     (eq x)
        eq' : (x x' : R) → (x - x' ∈ I) → left· x ≡ left· x'
        eq' x x' x-x'∈I i y = elimProp (λ y → squash/ (left· x y) (left· x' y))
                                       (λ y → eq′ y)
                                       y i
                              where
                                eq′ : (y : R) → left· x [ y ] ≡ left· x' [ y ]
                                eq′ y = eq/ (x · y) (x' · y)
                                            (subst (λ u → u ∈ I)
                                              ((x - x') · y         ≡⟨ ring-ldist x (- x') y ⟩
                                               x · y + (- x') · y   ≡⟨ cong
                                                                         (λ u → x · y + u)
                                                                         (-commutesWithLeft-· x' y) ⟩
                                               x · y - x' · y       ∎)
                                              (isIdeal.·-closedRight I-isIdeal y x-x'∈I))


    -- more or less copy paste from '+/I' - this is preliminary anyway
    ·/I-assoc : (x y z : R/I) → x ·/I (y ·/I z) ≡ (x ·/I y) ·/I z
    ·/I-assoc = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where eq : (x y z : R) → [ x ] ·/I ([ y ] ·/I [ z ]) ≡ ([ x ] ·/I [ y ]) ·/I [ z ]
            eq x y z i =  [ ring·-assoc x y z i ]

    ·/I-lid : (x : R/I) → 1/I ·/I x ≡ x
    ·/I-lid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → 1/I ·/I [ x ] ≡ [ x ]
        eq x i = [ ring·-lid x i ]

    ·/I-rid : (x : R/I) → x ·/I 1/I ≡ x
    ·/I-rid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] ·/I 1/I ≡ [ x ]
        eq x i = [ ring·-rid x i ]


    /I-ldist : (x y z : R/I) → (x +/I y) ·/I z ≡ (x ·/I z) +/I (y ·/I z)
    /I-ldist = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where
        eq : (x y z : R) → ([ x ] +/I [ y ]) ·/I [ z ] ≡ ([ x ] ·/I [ z ]) +/I ([ y ] ·/I [ z ])
        eq x y z i = [ ring-ldist x y z i ]

    /I-rdist : (x y z : R/I) → x ·/I (y +/I z) ≡ (x ·/I y) +/I (x ·/I z)
    /I-rdist = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where
        eq : (x y z : R) → [ x ] ·/I ([ y ] +/I [ z ]) ≡ ([ x ] ·/I [ y ]) +/I ([ x ] ·/I [ z ])
        eq x y z i = [ ring-rdist x y z i ]

  asRing : Ring {ℓ}
  asRing = createRing R/I isSetR/I
           (record
              { 0r = 0/I
              ; 1r = 1/I
              ; _+_ = _+/I_
              ; -_ = -/I
              ; _·_ = _·/I_
              ; +-assoc = +/I-is-associative
              ; +-rid = +/I-rid
              ; +-comm = +/I-comm
              ; +-rinv = +/I-rinv
              ; ·-assoc = ·/I-assoc
              ; ·-lid = ·/I-lid
              ; ·-rid = ·/I-rid
              ; ldist = /I-ldist
              ; rdist = /I-rdist
              })
