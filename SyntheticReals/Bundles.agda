{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Bundles where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Structures.Poset
open import Cubical.Foundations.Function
open import Cubical.Structures.Ring
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_)

open import Function.Base using (_∋_)
-- open import Function.Reasoning using (∋-syntax)
open import Function.Base using (it) -- instance search

open import Utils
open import MoreLogic
open MoreLogic.Reasoning
open MoreLogic.Properties
open import MoreAlgebra
open MoreAlgebra.Definitions
open MoreAlgebra.Consequences

-- 4.1  Algebraic structure of numbers
--
-- Fields have the property that nonzero numbers have a multiplicative inverse, or more precisely, that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.
--
-- Remark 4.1.1.
-- If we require the collection of numbers to form a set in the sense of Definition 2.5.4, and satisfy the ring axioms, then multiplicative inverses are unique, so that the above is equivalent to the proposition
--   (Π x : F) x ≠ 0 ⇒ (Σ y : F) x · y = 1.
--
-- Definition 4.1.2.
-- A classical field is a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

module ClassicalFieldModule where
  record IsClassicalField {F : Type ℓ}
                          (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_⁻¹ᶠ : (x : F) → {{¬(x ≡ 0f)}} → F) : Type ℓ where
    constructor isclassicalfield

    field
      isCommRing : IsCommRing 0f 1f _+_ _·_ -_
      ·-rinv : (x : F) → (p : ¬(x ≡ 0f)) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
      ·-linv : (x : F) → (p : ¬(x ≡ 0f)) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f

    open IsCommRing {0r = 0f} {1r = 1f} isCommRing public

  record ClassicalField : Type (ℓ-suc ℓ) where
    field
      Carrier : Type ℓ
      0f   : Carrier
      1f   : Carrier
      _+_  : Carrier → Carrier → Carrier
      _·_  : Carrier → Carrier → Carrier
      -_   : Carrier → Carrier
      _⁻¹ᶠ : (x : Carrier) → {{¬(x ≡ 0f)}} → Carrier
      isClassicalField : IsClassicalField 0f 1f _+_ _·_ -_ _⁻¹ᶠ

    infix  9 _⁻¹ᶠ
    infix  8 -_
    infixl 7 _·_
    infixl 6 _+_

    open IsClassicalField isClassicalField public

-- Remark 4.1.3.
-- As in the classical case, by proving that additive and multiplicative inverses are unique, we also obtain the negation and division operations.
--
-- For the reals, the assumption x ≠ 0 does not give us any information allowing us to bound x away from 0, which we would like in order to compute multiplicative inverses.
-- Hence, we give a variation on the denition of fields in which the underlying set comes equipped with an apartness relation #, which satises x # y ⇒ x ≠ y, although the converse implication may not hold.
-- This apartness relation allows us to make appropriate error bounds and compute multiplicative inverses based on the assumption x # 0.
--

-- NOTE: there is also PropRel in Cubical.Relation.Binary.Base which
-- NOTE: one needs these "all-lowercase constructors" to make use of copatterns
-- NOTE: see also Relation.Binary.Indexed.Homogeneous.Definitions.html
-- NOTE: see also Algebra.Definitions.html

-- Definition 4.1.5.
-- A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. x : F has a multiplicative inverse iff x # 0;
-- 3. + is #-extensional, that is, for all w, x, y, z : F
--    w + x # y + z ⇒ w # y ∨ x # z.

record IsConstructiveField {F : Type ℓ}
                           (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_#_ : hPropRel F F ℓ') (_⁻¹ᶠ : (x : F) → {{[ x # 0f ]}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isconstructivefield

  field
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    ·-rinv     : ∀ x → (p : [ x # 0f ]) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : ∀ x → (p : [ x # 0f ]) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    ·-inv-back : ∀ x y → (x · y ≡ 1f) → [ x # 0f ] × [ y # 0f ]
    #-tight    : ∀ x y → ¬([ x # y ]) → x ≡ y
    -- NOTE: the following ⊎ caused trouble two times with resolving ℓ or ℓ'
    +-#-extensional : ∀ w x y z → [ (w + x) # (y + z) ] → [ (w # y) ⊔ (x # z) ]
    isApartnessRel  : IsApartnessRelᵖ _#_

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsApartnessRelᵖ isApartnessRel public
    renaming
      ( isIrrefl  to #-irrefl
      ; isSym     to #-sym
      ; isCotrans to #-cotrans )

record ConstructiveField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor constructivefield
  field
    Carrier : Type ℓ
    0f   : Carrier
    1f   : Carrier
    _+_  : Carrier → Carrier → Carrier
    _·_  : Carrier → Carrier → Carrier
    -_   : Carrier → Carrier
    _#_  : hPropRel Carrier Carrier ℓ'
    _⁻¹ᶠ : (x : Carrier) → {{[ x # 0f ]}} → Carrier
    isConstructiveField : IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_

  open IsConstructiveField isConstructiveField public

-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.

record IsLattice {A : Type ℓ}
                 (_≤_ : Rel A A ℓ') (min max : A → A → A) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    isPartialOrder : IsPartialOrder _≤_
    glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
    glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
    lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
    lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z

  open IsPartialOrder isPartialOrder public
    renaming
      ( isRefl    to ≤-refl
      ; isAntisym to ≤-antisym
      ; isTrans   to ≤-trans )

record Lattice : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor lattice
  field
    Carrier : Type ℓ
    _≤_ : Rel Carrier Carrier ℓ'
    min max : Carrier → Carrier → Carrier
    isLattice : IsLattice _≤_ min max

  infixl 4 _≤_

  open IsLattice isLattice public

-- Remark 4.1.9.2
-- 1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that for every x and y, min(x,y) = x ∨ min(x,y) = y. However, we can characterize min as
--   z < min(x,y) ⇔ z < x ∨ z < y
--   and similarly for max, see Lemma 6.7.1.
-- 2. In a partial order, for two fixed elements a and b, all joins and meets of a, b are equal, so that Lemma 2.6.20 the type of joins and the type of meets are propositions. Hence, providing the maps min and max as in the above definition is equivalent to the showing the existenceof all binary joins and meets.
--
-- The following definition is modified from on The Univalent Foundations Program [89, Definition 11.2.7].
--
-- Definition 4.1.10.
-- An ordered field is a set F together with constants 0, 1, operations +, ·, min, max, and a binary relation < such that:
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. < is a strict [partial] order;
-- 3. x : F has a multiplicative inverse iff x # 0, recalling that # is defined as in Lemma 4.1.7;
-- 4. ≤, as in Lemma 4.1.7, is antisymmetric, so that (F, ≤) is a partial order;
-- 5. (F, ≤, min, max) is a lattice.
-- 6. for all x, y, z, w : F:
--    x + y < z + w ⇒ x < z ∨ y < w, (†)
--    0 < z ∧ x < y ⇒ x z < y z.     (∗)
-- Our notion of ordered fields coincides with The Univalent Foundations Program [89, Definition 11.2.7].

-- NOTE: well, the HOTT book definition organizes things slightly different. Why prefer one approach over the other?

record IsAlmostOrderedField {F : Type ℓ}
                 (0f 1f : F) (_+_ : F → F → F) (-_ : F → F) (_·_ min max : F → F → F) (_<_ _#_ _≤_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  field
    -- 1.
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    -- 2.
    <-isStrictPartialOrder : IsStrictPartialOrder _<_
    -- 3.
    ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    -- 4. NOTE: we already have ≤-isPartialOrder in <-isLattice
    -- ≤-isPartialOrder : IsPartialOrder _≤_
    -- 5.
    ≤-isLattice : IsLattice _≤_ min max

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsStrictPartialOrder <-isStrictPartialOrder public
    renaming
      ( isIrrefl  to <-irrefl
      ; isTrans   to <-trans
      ; isCotrans to <-cotrans )
  open IsLattice ≤-isLattice public

record AlmostOrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : Rel Carrier Carrier ℓ'
    <-isProp : ∀ x y → isProp (x < y)

  _#_ = _#'_ {_<_ = _<_}
  _≤_ = _≤'_ {_<_ = _<_}

  field
    _⁻¹ᶠ    : (x : Carrier) → {{x # 0f}} → Carrier
    isAlmostOrderedField : IsAlmostOrderedField 0f 1f _+_ -_ _·_ min max _<_ _#_ _≤_ _⁻¹ᶠ

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_

  open IsAlmostOrderedField isAlmostOrderedField public

  #-isProp : ∀ x y → isProp (x # y)
  #-isProp = #-from-<-isProp _<_ <-isStrictPartialOrder <-isProp

record IsOrderedField {F : Type ℓ}
                 (0f 1f : F) (_+_ : F → F → F) (-_ : F → F) (_·_ min max : F → F → F) (_<_ _#_ _≤_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isorderedfield
  field
    -- 1. 2. 3. 4. 5.
    isAlmostOrderedField : IsAlmostOrderedField 0f 1f _+_ -_ _·_ min max _<_ _#_ _≤_ _⁻¹ᶠ
    -- 6. (†)
    -- NOTE: this is 'shifted' from the pevious definition of #-extensionality for + .. does the name still fit?
    +-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
    -- 6. (∗)
    ·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z)
  open IsAlmostOrderedField isAlmostOrderedField public

record OrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : Rel Carrier Carrier ℓ'
    <-isProp : ∀ x y → isProp (x < y)

  _#_ = _#'_ {_<_ = _<_}
  _≤_ = _≤'_ {_<_ = _<_}

  field
    _⁻¹ᶠ    : (x : Carrier) → {{x # 0f}} → Carrier
    isOrderedField : IsOrderedField 0f 1f _+_ -_ _·_ min max _<_ _#_ _≤_ _⁻¹ᶠ

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_

  open IsOrderedField isOrderedField public

  abstract
    -- NOTE: there might be some reason not to "do" (or "open") all the theory of a record within that record
    +-preserves-< : ∀ a b x → a < b → a + x < b + x
    +-preserves-< a b x a<b = (
       a            <  b            ⇒⟨ transport (λ i → sym (fst (+-identity a)) i < sym (fst (+-identity b)) i) ⟩
       a +    0f    <  b +    0f    ⇒⟨ transport (λ i → a + sym (+-rinv x) i < b + sym (+-rinv x) i) ⟩
       a + (x  - x) <  b + (x  - x) ⇒⟨ transport (λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
      (a +  x) - x  < (b +  x) - x  ⇒⟨ +-<-extensional (- x) (a + x) (- x) (b + x) ⟩
      (a + x < b + x) ⊎ (- x < - x) ⇒⟨ (λ{ (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                         ; (inr  -x<-x ) → ⊥-elim {A = λ _ → (a + x < b + x)} (<-irrefl (- x) -x<-x) }) ⟩
       a + x < b + x ◼) a<b

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder = ≤-isPreorder' {_<_ = _<_} {<-isStrictPartialOrder}

-- Definition 4.3.1.
-- A morphism from an ordered field (F, 0F , 1F , +F , ·F , minF , maxF , <F )
--              to an ordered field (G, 0G , 1G , +G , ·G , minG , maxG , <G )
-- is a map f : F → G such that
-- 1. f is a morphism of rings,
-- 2. f reflects < in the sense that for every x, y : F
--    f (x) <G f (y) ⇒ x <F y.

-- NOTE: see Cubical.Structures.Group.Morphism
--       and Cubical.Structures.Group.MorphismProperties

-- open import Cubical.Structures.Group.Morphism

record IsRingMor
  {ℓ ℓ'}
  (F : Ring {ℓ}) (G : Ring {ℓ'})
  (f : (Ring.Carrier F) → (Ring.Carrier G)) : Type (ℓ-max ℓ ℓ')
  where
  module F = Ring F
  module G = Ring G
  field
    preserves-+ : ∀ a b → f (a F.+ b) ≡ f a G.+ f b
    preserves-· : ∀ a b → f (a F.· b) ≡ f a G.· f b
    perserves-1 : f F.1r ≡ G.1r

record IsOrderedFieldMor
  {ℓ ℓ' ℓₚ ℓₚ'} -- NOTE: this is a lot of levels. Can we get rid of some of these?
  (F : OrderedField {ℓ} {ℓₚ}) (G : OrderedField {ℓ'} {ℓₚ'})
  -- (let module F = OrderedField F) -- NOTE: `let` is not allowed in a telescope
  -- (let module G = OrderedField G)
  (f : (OrderedField.Carrier F) → (OrderedField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  module F = OrderedField F
  module G = OrderedField G
  field
    isRingMor : IsRingMor (record {F}) (record {G}) f
    reflects-< : ∀ x y → f x G.< f y → x F.< y
  -- NOTE: for more properties, see https://en.wikipedia.org/wiki/Ring_homomorphism#Properties

record OrderedFieldMor {ℓ ℓ' ℓₚ ℓₚ'} (F : OrderedField {ℓ} {ℓₚ}) (G : OrderedField {ℓ'} {ℓₚ'}) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ')) where
  constructor orderedfieldmor
  module F = OrderedField F
  module G = OrderedField G
  field
    fun : F.Carrier → G.Carrier
    isOrderedFieldMor : IsOrderedFieldMor F G fun

-- NOTE: f preserves P: P A ⇒ P (f A)
--       f reflects  P: P (f A) ⇒ P A
-- Remark 4.3.2. The contrapositive of reflecting < means preserving ≤.
