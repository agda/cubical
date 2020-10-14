{-# OPTIONS --cubical --no-import-sorts  #-}

module SyntheticReals.MoreAlgebra where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)

open import SyntheticReals.Utils

hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
hPropRel A B ℓ' = A → B → hProp ℓ'

module Definitions where
  -- NOTE: one needs these "all-lowercase constructors" to make use of copatterns

  _Preserves_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
  f Preserves P ⟶ Q = ∀{x y} → P x y → Q (f x) (f y)

  _Reflects_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
  f Reflects P ⟶ Q = ∀{x y} → Q (f x) (f y) → P x y

  -- https://en.wikipedia.org/wiki/Complete_partial_order
  --   A partially ordered set is a directed-complete partial order (dcpo) if each of its directed subsets has a supremum.
  --   A subset of a partial order is directed if it is non-empty and every pair of elements has an upper bound in the subset.
  --   In the literature, dcpos sometimes also appear under the label up-complete poset.

  -- https://ncatlab.org/nlab/show/dcpo
  --   A DCPO, or directed-complete partial order, is a poset with all directed joins.
  --   Often a DCPO is required to have a bottom element ⊥\bot; then it is called a pointed DCPO or a CPO (but this term is ambiguous).

  -- In this chapter we develop the theory of directed-complete partial orders (dcpo), namely
  -- partially ordered sets in which only certain joins are required to exist.
  --
  -- ...
  --
  -- 3.1 Dcpos
  --
  -- We start by defining partial orders. By a binary relation R on a set X , we mean a map X → X → HProp, as in Definition 2.7.1.
  -- We can specify which universe the binary relation lands in by saying that R is HPropᵢ-valued or is a relation in universe i if R : X → X → HPropᵢ.
  --
  -- Definition 3.1.1. A binary relation R on a set X is
  --
  -- 1. reflexive     if (∀ x       : X)   R x x;
  -- 2. irreflexive   if (∀ x       : X) ¬ R x x;
  -- 3. symmetric     if (∀ x, y    : X)   R x y ⇒ R y x;
  -- 4. antisymmetric if (∀ x, y    : X)   R x y ⇒ R y x ⇒ x = y;
  -- 5. transitive    if (∀ x, y, z : X)   R x y ⇒ R y z ⇒ R x z;
  -- 6. cotransitive  if (∀ x, y, z : X)   R x y ⇒ (R x z) ∨ (R z y).
  --
  -- Remark 3.1.2. Cotransitivity is also known as weak linearity [91, Definition 11.2.7] or the approximate splitting principle [84].
  --
  -- Definition 3.1.3.
  --
  -- A preorder, denoted by ≤, is a reflexive transitive relation.
  -- A partial order is an antisymmetric preorder.

  -- Definition 4.1.4.
  -- - An apartness relation, denoted by #, is an irreflexive symmetric cotransitive relation.
  -- - A strict partial order, denoted by <, is an irreflexive transitive cotransitive relation.

  IsIrrefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsIrrefl {A = A} R = (a : A) → ¬(R a a)

  IsCotrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsCotrans {A = A} R = (a b : A) → R a b → (∀(x : A) → (R a x) ⊎ (R x b))

  -- NOTE: see Cubical.Algebra.Poset
  IsSymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsSymᵖ {A = A} R = (a b : A) → [ R a b ] → [ R b a ]

  IsIrreflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsIrreflᵖ {A = A} R = (a : A) → [ ¬ᵖ(R a a) ]

  IsCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsCotransᵖ {A = A} R = (a b : A) → [ R a b ] → (∀(x : A) → [ (R a x) ⊔ (R x b) ])

  {- NOTE: formulating the properties on witnesses with `[_]` is similar to the previous Propositions-as-types formalism
           but it is not the way to proceed with hProps
           the idea is, to produce an hProp again
           e.g. from `Cubical.Algebra.Poset`
             isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
             isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = φ , φ-prop
               where
                 φ      : Type (ℓ-max ℓ₀ ℓ₁)
                 φ      = ((x y z : X) → [ x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z ])
                 φ-prop : isProp φ
                 φ-prop = isPropΠ3 λ x y z → snd (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)
  -}
  IsTransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTransᵖ {A = A} R = (a b c : A)  → [ R a b ] → [ R b c ] → [ R a c ]

  -- NOTE: this is starting with a lower-case, because `hProp (ℓ-max ℓ ℓ')` is not a type but an element
  isTransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
    where
      φ : Type (ℓ-max ℓ ℓ')
      φ = (a b c : A) → [ R a b ⇒ R b c ⇒ R a c ]
      φ-prop : isProp φ
      φ-prop = isPropΠ3 λ a b c → snd (R a b ⇒ R b c ⇒ R a c)

  isIrreflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isIrreflᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
    where
      φ : Type (ℓ-max ℓ ℓ')
      φ = (a : A) → [ ¬ᵖ (R a a) ]
      φ-prop : isProp φ
      φ-prop = isPropΠ λ a → snd (¬ᵖ (R a a))

  isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isCotransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
    where
      φ : Type (ℓ-max ℓ ℓ')
      φ = (a b : A) → [ R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)) ]
      φ-prop : isProp φ
      φ-prop = isPropΠ2 λ a b → snd (R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)))

  record IsApartnessRel {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      isIrrefl  : IsIrrefl R
      isSym     : BinaryRelation.isSym R
      isCotrans : IsCotrans R

  record IsApartnessRelᵖ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      isIrrefl  : IsIrreflᵖ R
      isSym     : IsSymᵖ R
      isCotrans : IsCotransᵖ R

  record IsStrictPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorder
    field
      isIrrefl  : IsIrrefl R
      isTrans   : BinaryRelation.isTrans R
      isCotrans : IsCotrans R

  record IsStrictPartialOrderᵖ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorderᵖ
    field
      isIrrefl  : IsIrreflᵖ R
      isTrans   : IsTransᵖ R
      isCotrans : IsCotransᵖ R

  {- NOTE: here again, the previous-way-interpretation would be to put witnesses into the struct with `[_]`
           but with hProps, we would have `isStrictPartialOrder : hProp`
           and use `[ isStrictPartialOrder ]` as the witness type
           with hProps we would need to make heavy use of `Cubical.Foundations.HLevels`
             isProp×, isProp×2, isProp×3
           to show the record's `isProp`
           do we have pathes on records? in order to use `isProp` on records?
             yes, with record constructors
  -}
  record [IsStrictPartialOrder] {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorderᵖ
    field
      isIrrefl  : [ isIrreflᵖ  R ]
      isTrans   : [ isTransᵖ   R ]
      isCotrans : [ isCotransᵖ R ]

  isStrictParialOrder : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isStrictParialOrder R = [IsStrictPartialOrder] R , φ-prop where
    φ-prop :      isProp ([IsStrictPartialOrder] R)
    φ-prop (isstrictpartialorderᵖ isIrrefl₀ isTrans₀ isCotrans₀)
           (isstrictpartialorderᵖ isIrrefl₁ isTrans₁ isCotrans₁) =
      λ i → isstrictpartialorderᵖ (isProp[] (isIrreflᵖ  R) isIrrefl₀  isIrrefl₁  i)
                                  (isProp[] (isTransᵖ   R) isTrans₀   isTrans₁   i)
                                  (isProp[] (isCotransᵖ R) isCotrans₀ isCotrans₁ i)

  record IsPreorder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor ispreorder
    field
      isRefl    : BinaryRelation.isRefl R
      isTrans   : BinaryRelation.isTrans R

  -- NOTE: there is already
  --       isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
  --       in Cubical.Algebra.Poset. Can we use this?
  -- import Cubical.Algebra.Poset

  IsAntisym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsAntisym {A = A} R = ∀ a b → R a b → R b a → a ≡ b

  record IsPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor ispartialorder
    field
      isRefl    : BinaryRelation.isRefl R
      isAntisym : IsAntisym R
      isTrans   : BinaryRelation.isTrans R

  _#'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
  _#'_ {_<_ = _<_} x y = (x < y) ⊎ (y < x)

  _≤'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
  _≤'_ {_<_ = _<_} x y = ¬ (y < x)


-- NOTE: there is `Properties` and `Consequences`
--       the difference somehow is, that we do want to open `Consequences` directly
--       but we do not want to open `Properties` directly, because it might have a name clash
--       e.g. there is `Properties.Group` which clashes with `Cubical.Algebra.Group.Group` when opening `Properties`
--       but it is totally fine to open `Properties.Group` directly because it does not export a `Group`
-- TODO: check whether this matches the wording of the (old) standard library
module Consequences where
  open Definitions

  -- Lemma 4.1.7.
  -- Given a strict partial order < on a set X:
  -- 1. we have an apartness relation defined by
  --    x # y := (x < y) ∨ (y < x), and

  #'-isApartnessRel : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → (isSPO : IsStrictPartialOrder _<_) → IsApartnessRel (_#'_ {_<_ = _<_})
  #'-isApartnessRel {X = X} {_<_ = _<_} isSPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
    in λ where
      .IsApartnessRel.isIrrefl a (inl a<a) → <-irrefl _ a<a
      .IsApartnessRel.isIrrefl a (inr a<a) → <-irrefl _ a<a
      .IsApartnessRel.isSym    a b p → ⊎-swap p
      .IsApartnessRel.isCotrans a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where -- case x of f = f x
        (inl a<x) → inl (inl a<x)
        (inr x<b) → inr (inl x<b)
      .IsApartnessRel.isCotrans a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
        (inl b<x) → inr (inr b<x)
        (inr x<a) → inl (inr x<a)

  -- variant without copatterns: "just" move the `λ where` "into" the record
  #'-isApartnessRel' : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → {IsStrictPartialOrder _<_} → IsApartnessRel (_#'_ {_<_ = _<_})
  #'-isApartnessRel' {X = X} {_<_ = _<_} {isSPO} =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
    in record
      { isIrrefl  = λ where a (inl a<a) → <-irrefl _ a<a
                            a (inr a<a) → <-irrefl _ a<a
      ; isSym     = λ where a b p → ⊎-swap p
      ; isCotrans = λ where
        a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where
          (inl a<x) → inl (inl a<x)
          (inr x<b) → inr (inl x<b)
        a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
          (inl b<x) → inr (inr b<x)
          (inr x<a) → inl (inr x<a)
      }

  -- 2. we have a preorder defined by
  --    x ≤ y := ¬(y < x).

  ≤-isPreorder' : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → {IsStrictPartialOrder _<_} → IsPreorder (_≤'_ {_<_ = _<_})
  ≤-isPreorder' {X = X} {_<_ = _<_} {isSPO} =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
    in λ where
     .IsPreorder.isRefl → <-irrefl
     .IsPreorder.isTrans a b c ¬b<a ¬c<b c<a → case (<-cotrans _ _ c<a b) of λ where
       (inl c<b) → ¬c<b c<b
       (inr b<a) → ¬b<a b<a

  module _
    {X : Type ℓ} (_<_ : Rel X X ℓ')
    (isSPO : IsStrictPartialOrder _<_)
    (<-isProp : ∀ x y → isProp (x < y))
    (let _#_ = _#'_ {_<_ = _<_})
    (let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO)
    where
    -- open IsStrictPartialOrder isSPO

    #-from-<-isProp : ∀ x y → isProp (x # y)
    #-from-<-isProp x y (inl x<y₁) (inl x<y₂) = cong inl (<-isProp x y x<y₁ x<y₂)
    -- NOTE: ⊥-elim could not resolve the level here and needed some hint on `A`
    #-from-<-isProp x y (inl x<y ) (inr y<x ) = ⊥-elim {A = λ _ → inl x<y ≡ inr y<x} (<-irrefl y (<-trans y x y y<x x<y))
    #-from-<-isProp x y (inr y<x ) (inl x<y ) = ⊥-elim {A = λ _ → inr y<x ≡ inl x<y} (<-irrefl y (<-trans y x y y<x x<y))
    #-from-<-isProp x y (inr y<x₁) (inr y<x₂) = cong inr (<-isProp y x y<x₁ y<x₂)

module Properties where

  module _ where
    open import Cubical.Algebra.Group
    -- import Cubical.Algebra.Group.Properties

    module GroupProperties (G : Group {ℓ}) where
      open Group G
      private
        simplR = GroupLemmas.simplR G

      invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
      invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

      -- ported from `Algebra.Properties.Group`
      right-helper : ∀ x y → y ≡ - x + (x + y)
      right-helper x y = (
        y               ≡⟨ sym (snd (identity y)) ⟩
        0g          + y ≡⟨ cong₂ _+_ (sym (snd (inverse x))) refl  ⟩
        ((- x) + x) + y ≡⟨ sym (assoc (- x) x y) ⟩
        (- x) + (x + y) ∎)

      -- alternative:
      --   follows from uniqueness of -
      --     (a + -a) ≡ 0
      --     ∃! b . a + b = 0
      --   show that a is an additive inverse of - a then it must be THE additive inverse of - a and has to be called - - a which is a by uniqueness
      -involutive : ∀ x → - - x ≡ x
      -involutive x = (
        (- (- x))             ≡⟨ sym (fst (identity _)) ⟩
        (- (- x)) + 0g        ≡⟨ cong₂ _+_ refl (sym (snd (inverse _))) ⟩
        (- (- x)) + (- x + x) ≡⟨ sym (right-helper (- x) x) ⟩
        x                    ∎)

  module _ where
    open import Cubical.Algebra.Ring
    module RingProperties (R : Ring {ℓ}) where
      open Ring R
      open Cubical.Algebra.Ring.Theory R

      -- NOTE: a few facts about rings that might be collected from elsewhere
      a+b-b≡a : ∀ a b → a ≡ (a + b) - b
      a+b-b≡a a b = let P = sym (fst (+-inv b))
                        Q = sym (fst (+-identity a))
                        R = transport (λ i → a ≡ a + P i) Q
                        S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
                    in S

      -- NOTE: this is called `simplL` and `simplL` in `Cubical.Algebra.Group.Properties.GroupLemmas`
      +-preserves-≡ : ∀{a b} → ∀ c → a ≡ b → a + c ≡ b + c
      +-preserves-≡ c a≡b i = a≡b i + c

      +-preserves-≡-l : ∀{a b} → ∀ c → a ≡ b → c + a ≡ c + b
      +-preserves-≡-l c a≡b i = c + a≡b i

      a+b≡0→a≡-b : ∀{a b} → a + b ≡ 0r → a ≡ - b
      a+b≡0→a≡-b {a} {b} a+b≡0 = transport
        (λ i →
          let RHS = snd (+-identity (- b))
              LHS₁ : a + (b + - b) ≡ a + 0r
              LHS₁ = +-preserves-≡-l a (fst (+-inv b))
              LHS₂ : (a + b) - b ≡ a
              LHS₂ = transport (λ j →  (+-assoc a b (- b)) j ≡ fst (+-identity a) j) LHS₁
              in  LHS₂ i ≡ RHS i
        ) (+-preserves-≡ (- b) a+b≡0)

      -- NOTE: there is already
      -- -commutesWithRight-· : (x y : R) →  x · (- y) ≡ - (x · y)

      a·-b≡-a·b : ∀ a b → a · (- b) ≡ - (a · b)
      a·-b≡-a·b a b =
        let P : a · 0r ≡ 0r
            P = 0-rightNullifies a
            Q : a · (- b + b) ≡ 0r
            Q = transport (λ i →  a · snd (+-inv b) (~ i) ≡ 0r) P
            R : a · (- b) + a · b ≡ 0r
            R = transport (λ i → ·-rdist-+ a (- b) b i ≡ 0r) Q
        in a+b≡0→a≡-b R

      a·b-a·c≡a·[b-c] : ∀ a b c → a · b - (a · c) ≡ a · (b - c)
      a·b-a·c≡a·[b-c] a b c =
        let P : a · b + a · (- c) ≡ a · (b + - c)
            P = sym (·-rdist-+ a b (- c))
            Q : a · b - a · c ≡ a · (b + - c)
            Q = transport (λ i →  a · b + a·-b≡-a·b a c i ≡ a · (b + - c) ) P
        in  Q

  -- exports
  module Group = GroupProperties
  module Ring  = RingProperties
