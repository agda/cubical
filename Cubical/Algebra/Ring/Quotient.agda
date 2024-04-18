{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_; ⊆-extensionality) -- \in, \sub=
open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma using (Σ≡Prop)

open import Cubical.Relation.Binary

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/ₛ_)
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal
open import Cubical.Algebra.Ring.Kernel

private
  variable
    ℓ ℓ' : Level

module _ (R' : Ring ℓ) (I : ⟨ R' ⟩  → hProp ℓ) (I-isIdeal : isIdeal R' I) where
  open RingStr (snd R')
  private R = ⟨ R' ⟩
  open isIdeal I-isIdeal
  open RingTheory R'

  R/I : Type ℓ
  R/I = R /ₛ (λ x y → x - y ∈ I)

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
                      ((a + x) - (a + y))   ≡⟨ cong (λ u → u - (a + y)) (+Comm _ _) ⟩
                      ((x + a) - (a + y))   ≡⟨ cong (λ u → (x + a) - u) (+Comm _ _) ⟩
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

    -- Note that _+/I_ reduces in this case:
    _ : (x y : R) → [ x ] +/I [ y ] ≡ [ x + y ]
    _ = λ x y → refl

    +/I-comm : (x y : R/I) → x +/I y ≡ y +/I x
    +/I-comm = elimProp2 (λ _ _ → squash/ _ _) eq
       where eq : (x y : R) → [ x ] +/I [ y ] ≡ [ y ] +/I [ x ]
             eq x y i =  [ +Comm x y i ]

    +/I-assoc : (x y z : R/I) → x +/I (y +/I z) ≡ (x +/I y) +/I z
    +/I-assoc = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where eq : (x y z : R) → [ x ] +/I ([ y ] +/I [ z ]) ≡ ([ x ] +/I [ y ]) +/I [ z ]
            eq x y z i =  [ +Assoc x y z i ]


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
            eq' = - (x + (- y))       ≡⟨ sym (-Dist _ _) ⟩
                  (- x) - (- y)       ∎

    +/I-rinv : (x : R/I) → x +/I (-/I x) ≡ 0/I
    +/I-rinv = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I (-/I [ x ]) ≡ 0/I
        eq x i = [ +InvR x i ]


    +/I-rid : (x : R/I) → x +/I 0/I ≡ x
    +/I-rid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] +/I 0/I ≡ [ x ]
        eq x i = [ +IdR x i ]

    _·/I_ : R/I → R/I → R/I
    _·/I_ =
      elim (λ _ → isSetΠ (λ _ → squash/))
               (λ x → left· x)
               eq'
      where
        eq : (x y y' : R) → (y - y' ∈ I) → [ x · y ] ≡ [ x · y' ]
        eq x y y' y-y'∈I = eq/ _ _
                             (subst (λ u → u ∈ I)
                                  (x · (y - y')            ≡⟨ ·DistR+ _ _ _ ⟩
                                  ((x · y) + x · (- y'))   ≡⟨ cong (λ u → (x · y) + u)
                                                                   (-DistR· x y')  ⟩
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
                                              ((x - x') · y         ≡⟨ ·DistL+ x (- x') y ⟩
                                               x · y + (- x') · y   ≡⟨ cong
                                                                         (λ u → x · y + u)
                                                                         (-DistL· x' y) ⟩
                                               x · y - x' · y       ∎)
                                              (isIdeal.·-closedRight I-isIdeal y x-x'∈I))


    -- more or less copy paste from '+/I' - this is preliminary anyway
    ·/I-assoc : (x y z : R/I) → x ·/I (y ·/I z) ≡ (x ·/I y) ·/I z
    ·/I-assoc = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where eq : (x y z : R) → [ x ] ·/I ([ y ] ·/I [ z ]) ≡ ([ x ] ·/I [ y ]) ·/I [ z ]
            eq x y z i =  [ ·Assoc x y z i ]

    ·/I-lid : (x : R/I) → 1/I ·/I x ≡ x
    ·/I-lid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → 1/I ·/I [ x ] ≡ [ x ]
        eq x i = [ ·IdL x i ]

    ·/I-rid : (x : R/I) → x ·/I 1/I ≡ x
    ·/I-rid = elimProp (λ x → squash/ _ _) eq
      where
        eq : (x : R) → [ x ] ·/I 1/I ≡ [ x ]
        eq x i = [ ·IdR x i ]


    /I-ldist : (x y z : R/I) → (x +/I y) ·/I z ≡ (x ·/I z) +/I (y ·/I z)
    /I-ldist = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where
        eq : (x y z : R) → ([ x ] +/I [ y ]) ·/I [ z ] ≡ ([ x ] ·/I [ z ]) +/I ([ y ] ·/I [ z ])
        eq x y z i = [ ·DistL+ x y z i ]

    /I-rdist : (x y z : R/I) → x ·/I (y +/I z) ≡ (x ·/I y) +/I (x ·/I z)
    /I-rdist = elimProp3 (λ _ _ _ → squash/ _ _) eq
      where
        eq : (x y z : R) → [ x ] ·/I ([ y ] +/I [ z ]) ≡ ([ x ] ·/I [ y ]) +/I ([ x ] ·/I [ z ])
        eq x y z i = [ ·DistR+ x y z i ]

  asRing : Ring ℓ
  asRing = makeRing 0/I 1/I _+/I_ _·/I_ -/I isSetR/I
                    +/I-assoc +/I-rid +/I-rinv +/I-comm
                    ·/I-assoc ·/I-rid ·/I-lid /I-rdist /I-ldist

_/_ : (R : Ring ℓ) → (I : IdealsIn R) → Ring ℓ
R / (I , IisIdeal) = asRing R I IisIdeal

[_]/I : {R : Ring ℓ} {I : IdealsIn R} → (a : ⟨ R ⟩) → ⟨ R / I ⟩
[ a ]/I = [ a ]

quotientHom : (R : Ring ℓ) → (I : IdealsIn R) → RingHom R (R / I)
fst (quotientHom R I) = [_]
IsRingHom.pres0 (snd (quotientHom R I)) = refl
IsRingHom.pres1 (snd (quotientHom R I)) = refl
IsRingHom.pres+ (snd (quotientHom R I)) _ _ = refl
IsRingHom.pres· (snd (quotientHom R I)) _ _ = refl
IsRingHom.pres- (snd (quotientHom R I)) _ = refl

quotientHomSurjective : (R : Ring ℓ) → (I : IdealsIn R)
                        → isSurjection (fst (quotientHom R I))
quotientHomSurjective R I = []surjective


module UniversalProperty (R : Ring ℓ) (I : IdealsIn R) where
  open RingStr ⦃...⦄
  open RingTheory ⦃...⦄
  Iₛ = fst I
  private
    instance
      _ = snd R

  module _ {S : Ring ℓ'} (φ : RingHom R S) where
    open IsRingHom
    open RingHomTheory φ
    private
      instance
        _ = snd S
      f = fst φ
      module φ = IsRingHom (snd φ)

    {-
      We do not use the kernel ideal, since it is *not* an ideal in R,
      if S is from a different universe. Instead, the condition, that
      Iₛ is contained in the kernel of φ is rephrased explicitly.
    -}
    inducedHom : ((x : ⟨ R ⟩) → x ∈ Iₛ → φ $r x ≡ 0r) → RingHom (R / I) S
    fst (inducedHom Iₛ⊆kernel) =
      elim
        (λ _ → is-set)
        f
        λ r₁ r₂ r₁-r₂∈I → equalByDifference (f r₁) (f r₂)
          (f r₁ - f r₂     ≡⟨ cong (λ u → f r₁ + u) (sym (φ.pres- _)) ⟩
           f r₁ + f (- r₂) ≡⟨ sym (φ.pres+ _ _) ⟩
           f (r₁ - r₂)     ≡⟨ Iₛ⊆kernel (r₁ - r₂) r₁-r₂∈I ⟩
           0r ∎)
    pres0 (snd (inducedHom Iₛ⊆kernel)) = φ.pres0
    pres1 (snd (inducedHom Iₛ⊆kernel)) = φ.pres1
    pres+ (snd (inducedHom Iₛ⊆kernel)) =
      elimProp2 (λ _ _ → is-set _ _) φ.pres+
    pres· (snd (inducedHom Iₛ⊆kernel)) =
      elimProp2 (λ _ _ → is-set _ _) φ.pres·
    pres- (snd (inducedHom Iₛ⊆kernel)) =
      elimProp (λ _ → is-set _ _) φ.pres-

    solution : (p : ((x : ⟨ R ⟩) → x ∈ Iₛ → φ $r x ≡ 0r))
               → (x : ⟨ R ⟩) → inducedHom p $r [ x ] ≡ φ $r x
    solution p x = refl

    unique : (p : ((x : ⟨ R ⟩) → x ∈ Iₛ → φ $r x ≡ 0r))
             → (ψ : RingHom (R / I) S) → (ψIsSolution : (x : ⟨ R ⟩) → ψ $r [ x ] ≡ φ $r x)
             → (x : ⟨ R ⟩) → ψ $r [ x ] ≡ inducedHom p $r [ x ]
    unique p ψ ψIsSolution x = ψIsSolution x

{-
  Show that the kernel of the quotient map
  π : R ─→ R/I
  is the given ideal I.
-}
module idealIsKernel {R : Ring ℓ} (I : IdealsIn R) where
  open RingStr (snd R)
  open isIdeal (snd I)
  open BinaryRelation.isEquivRel

  private
    π = quotientHom R I
    x-0≡x : (x : ⟨ R ⟩) → x - 0r ≡ x
    x-0≡x x =
      x - 0r  ≡⟨ cong (x +_) (RingTheory.0Selfinverse R) ⟩
      x + 0r  ≡⟨ +IdR x ⟩
      x       ∎

  I⊆ker : fst I ⊆ kernel π
  I⊆ker x x∈I = eq/ _ _ (subst (_∈ fst I) (sym (x-0≡x x)) x∈I)

  private
    _~_ : Rel ⟨ R ⟩ ⟨ R ⟩ ℓ
    x ~ y = x - y ∈ fst I

    ~IsPropValued : BinaryRelation.isPropValued _~_
    ~IsPropValued x y = snd (fst I (x - y))

    -- _~_ is an equivalence relation.
    -- Note: This could be proved in the general setting of a subgroup of a group.

    -[x-y]≡y-x : {x y : ⟨ R ⟩} → - (x - y) ≡ y - x
    -[x-y]≡y-x {x} {y} =
      - (x - y)      ≡⟨ sym (-Dist _ _) ⟩
      - x + - (- y)  ≡⟨ cong (- x +_) (-Idempotent _) ⟩
      - x + y        ≡⟨ +Comm _ _ ⟩
      y - x          ∎
      where open RingTheory R

    x-y+y-z≡x-z : {x y z : ⟨ R ⟩} → (x - y) + (y - z) ≡ x - z
    x-y+y-z≡x-z {x} {y} {z} =
      (x + - y) + (y + - z)  ≡⟨ +Assoc _ _ _ ⟩
      ((x + - y) + y) + - z  ≡⟨ cong (_+ - z) (sym (+Assoc _ _ _)) ⟩
      (x + (- y + y)) + - z  ≡⟨ cong (λ -y+y → (x + -y+y) + - z) (+InvL _) ⟩
      (x + 0r) + - z         ≡⟨ cong (_+ - z) (+IdR _) ⟩
      x - z                  ∎

    ~IsEquivRel : BinaryRelation.isEquivRel _~_
    reflexive ~IsEquivRel x              = subst (_∈ fst I) (sym (+InvR x)) 0r-closed
    symmetric ~IsEquivRel x y x~y        = subst (_∈ fst I) -[x-y]≡y-x (-closed x~y)
    transitive ~IsEquivRel x y z x~y y~z = subst (_∈ fst I) x-y+y-z≡x-z (+-closed x~y y~z)

  ker⊆I : kernel π ⊆ fst I
  ker⊆I x x∈ker = subst (_∈ fst I) (x-0≡x x) x-0∈I
    where
      x-0∈I : x - 0r ∈ fst I
      x-0∈I = effective ~IsPropValued ~IsEquivRel x 0r x∈ker

kernel≡I :  {R : Ring ℓ} (I : IdealsIn R)
          → kernelIdeal (quotientHom R I) ≡ I
kernel≡I {R = R} I = Σ≡Prop (isPropIsIdeal R) (⊆-extensionality _ _ (ker⊆I , I⊆ker))
  where open idealIsKernel I
