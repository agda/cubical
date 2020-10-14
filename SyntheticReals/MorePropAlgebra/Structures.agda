{-# OPTIONS --cubical --no-import-sorts  #-}

module SyntheticReals.MorePropAlgebra.Structures where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_)
open import Cubical.Foundations.Function
-- open import Function.Reasoning using (∋-syntax)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax to infix  -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix  -4 ∃[∶]-syntax --
  ; ∀[∶]-syntax to infix  -4 ∀[∶]-syntax --
  ; ∀[]-syntax to infix  -4 ∀[]-syntax   --
  )

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax to infix -4 ∀〚∶〛-syntax
  )
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
open import SyntheticReals.MorePropAlgebra.Consequences

-- taken from the cubical standard library and adapted to hProps:
--   IsSemigroup
--   IsMonoid
--   IsGroup
--   IsAbGroup
--   IsRing
--   IsCommRing

record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where
  constructor issemigroup
  field
    is-set   : [ isSetᵖ A ]
    is-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z

  _ : [ isSetᵖ A                  ]; _ = is-set
  _ : [ isAssociativeˢ _·_ is-set ]; _ = is-assoc

isSemigroup : {A : Type ℓ} (_·_ : A → A → A) → hProp ℓ
isSemigroup _·_ .fst = IsSemigroup _·_
isSemigroup _·_ .snd (issemigroup a₀ b₀) (issemigroup a₁ b₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in issemigroup is-set (snd (isAssociativeˢ _·_ is-set) b₀ b₁ i)

record IsMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor ismonoid
  field
    is-Semigroup : [ isSemigroup _·_ ]
    is-identity  : ∀ x → (x · ε ≡ x) × (ε · x ≡ x)

  open IsSemigroup is-Semigroup public

  _ : [ isSemigroup _·_          ]; _ = is-Semigroup
  _ : [ isIdentityˢ _·_ is-set ε ]; _ = is-identity

  is-lid : (x : A) → ε · x ≡ x
  is-lid x = is-identity x .snd

  is-rid : (x : A) → x · ε ≡ x
  is-rid x = is-identity x .fst

isMonoid : {A : Type ℓ} (ε : A) (_·_ : A → A → A) → hProp ℓ
isMonoid ε _·_ .fst = IsMonoid ε _·_
isMonoid ε _·_ .snd (ismonoid a₀ b₀) (ismonoid a₁ b₁) = φ where
  abstract φ = λ i → let is-Semigroup = snd (isSemigroup _·_) a₀ a₁ i
                         is-set       = IsSemigroup.is-set is-Semigroup
                     in ismonoid is-Semigroup (snd (isIdentityˢ _·_ is-set ε) b₀ b₁ i)

record IsGroup {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where
  constructor isgroup
  field
    is-Monoid  : [ isMonoid 0g _+_ ]
    is-inverse : ∀ x → (x + (- x) ≡ 0g) × ((- x) + x ≡ 0g)

  open IsMonoid is-Monoid public

  _ : [ isMonoid 0g _+_             ]; _ = is-Monoid
  _ : [ isInverseˢ is-set 0g _+_ -_ ]; _ = is-inverse

  infixl 6 _-_

  _-_ : G → G → G
  x - y = x + (- y)

  is-invl : (x : G) → (- x) + x ≡ 0g
  is-invl x = is-inverse x .snd

  is-invr : (x : G) → x + (- x) ≡ 0g
  is-invr x = is-inverse x .fst

isGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) → hProp ℓ
isGroup 0g _+_ -_ .fst = IsGroup 0g _+_ -_
isGroup 0g _+_ -_ .snd (isgroup a₀ b₀) (isgroup a₁ b₁) = φ where
  abstract φ = λ i → let is-Monoid = snd (isMonoid 0g _+_) a₀ a₁ i
                         is-set    = IsMonoid.is-set is-Monoid
                     in isgroup is-Monoid (snd (isInverseˢ is-set 0g _+_ -_) b₀ b₁ i)

record IsAbGroup {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where
  constructor isabgroup
  field
    is-Group : [ isGroup 0g _+_ -_ ]
    is-comm  : ∀ x y → x + y ≡ y + x

  open IsGroup is-Group public

  _ : [ isGroup 0g _+_ (-_)       ]; _ = is-Group
  _ : [ isCommutativeˢ _+_ is-set ]; _ = is-comm

isAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) → hProp ℓ
isAbGroup 0g _+_ -_ .fst = IsAbGroup 0g _+_ -_
isAbGroup 0g _+_ -_ .snd (isabgroup a₀ b₀) (isabgroup a₁ b₁) = φ where
  abstract φ = λ i → let is-Group = snd (isGroup 0g _+_ -_) a₀ a₁ i
                         is-set   = IsGroup.is-set is-Group
                     in isabgroup is-Group (snd (isCommutativeˢ _+_ is-set) b₀ b₁ i)

record IsSemiring {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where
  constructor issemiring
  field
    +-Monoid  : [ isMonoid 0r _+_ ]
    ·-Monoid  : [ isMonoid 1r _·_ ]
    +-comm    : ∀ x y → x + y ≡ y + x
    is-dist   : ∀ x y z → (x · (y +  z) ≡ (x · y) + (x · z)) × ((x +  y) · z  ≡ (x · z) + (y · z))

  open IsMonoid +-Monoid public
    renaming
      ( is-assoc     to +-assoc
      ; is-identity  to +-identity
      ; is-lid       to +-lid
      ; is-rid       to +-rid
      ; is-Semigroup to +-Semigroup )

  open IsMonoid ·-Monoid hiding (is-set) public
    renaming
      ( is-assoc     to ·-assoc
      ; is-identity  to ·-identity
      ; is-lid       to ·-lid
      ; is-rid       to ·-rid
      ; is-Semigroup to ·-Semigroup )

  _ : [ isMonoid  0r _+_               ]; _ = +-Monoid
  _ : [ isMonoid  1r _·_               ]; _ = ·-Monoid
  _ : [ isCommutativeˢ _+_ is-set      ]; _ = +-comm
  _ : [ isDistributiveˢ is-set _+_ _·_ ]; _ = is-dist

isSemiring : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) → hProp ℓ
isSemiring 0r 1r _+_ _·_ .fst = IsSemiring 0r 1r _+_ _·_
isSemiring 0r 1r _+_ _·_ .snd (issemiring a₀ b₀ c₀ d₀) (issemiring a₁ b₁ c₁ d₁) = φ where
  abstract φ = λ i → let +-Monoid = snd (isMonoid 0r _+_) a₀ a₁ i
                         ·-Monoid = snd (isMonoid 1r _·_) b₀ b₁ i
                         is-set   = IsMonoid.is-set +-Monoid
                         +-comm   = snd (isCommutativeˢ _+_ is-set) c₀ c₁ i
                         is-dist  = snd (isDistributiveˢ is-set _+_ _·_) d₀ d₁ i
                     in issemiring +-Monoid ·-Monoid +-comm is-dist

record IsCommSemiring {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where
  constructor iscommsemiring
  field
    is-Semiring : [ isSemiring 0r 1r _+_ _·_ ]
    ·-comm    : ∀ x y → x · y ≡ y · x

  open IsSemiring is-Semiring public

  _ : [ isSemiring 0r 1r _+_ _·_       ]; _ = is-Semiring
  _ : [ isCommutativeˢ _+_ is-set      ]; _ = +-comm

isCommSemiring : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) → hProp ℓ
isCommSemiring 0r 1r _+_ _·_ .fst = IsCommSemiring 0r 1r _+_ _·_
isCommSemiring 0r 1r _+_ _·_ .snd (iscommsemiring a₀ b₀) (iscommsemiring a₁ b₁) = φ where
  abstract φ = λ i → let is-Semiring = snd (isSemiring 0r 1r _+_ _·_) a₀ a₁ i
                         is-set   = IsSemiring.is-set is-Semiring
                         ·-comm   = snd (isCommutativeˢ _·_ is-set) b₀ b₁ i
                     in iscommsemiring is-Semiring ·-comm

record IsRing {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
  constructor isring
  field
    +-AbGroup : [ isAbGroup 0r _+_ -_ ]
    ·-Monoid  : [ isMonoid  1r _·_ ]
    is-dist   : ∀ x y z → (x · (y +  z) ≡ (x · y) + (x · z)) × ((x +  y) · z  ≡ (x · z) + (y · z))

  open IsAbGroup +-AbGroup using (is-set) public

  _ : [ isAbGroup 0r _+_ -_            ]; _ = +-AbGroup
  _ : [ isMonoid  1r _·_               ]; _ = ·-Monoid
  _ : [ isDistributiveˢ is-set _+_ _·_ ]; _ = is-dist

  open IsAbGroup +-AbGroup hiding (is-set) public
    renaming
      ( is-assoc     to +-assoc
      ; is-identity  to +-identity
      ; is-lid       to +-lid
      ; is-rid       to +-rid
      ; is-inverse   to +-inv
      ; is-invl      to +-linv
      ; is-invr      to +-rinv
      ; is-comm      to +-comm
      ; is-Semigroup to +-Semigroup
      ; is-Monoid    to +-Monoid
      ; is-Group     to +-Group )

  open IsMonoid ·-Monoid hiding (is-set) public
    renaming
      ( is-assoc     to ·-assoc
      ; is-identity  to ·-identity
      ; is-lid       to ·-lid
      ; is-rid       to ·-rid
      ; is-Semigroup to ·-Semigroup )

  ·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·-rdist-+ x y z = is-dist x y z .fst

  ·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·-ldist-+ x y z = is-dist x y z .snd

  -- TODO: prove these somewhere

  -- zero-lid : (x : R) → 0r · x ≡ 0r
  -- zero-lid x = zero x .snd

  -- zero-rid : (x : R) → x · 0r ≡ 0r
  -- zero-rid x = zero x .fst

isRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) → hProp ℓ
isRing 0r 1r _+_ _·_ -_ .fst = IsRing 0r 1r _+_ _·_ -_
isRing 0r 1r _+_ _·_ -_ .snd (isring a₀ b₀ c₀) (isring a₁ b₁ c₁) = φ where
  abstract φ = λ i → let +-AbGroup = snd (isAbGroup 0r _+_ -_) a₀ a₁ i
                         ·-Monoid  = snd (isMonoid 1r _·_) b₀ b₁ i
                         is-set    = IsAbGroup.is-set +-AbGroup
                         is-dist   = snd (isDistributiveˢ is-set _+_ _·_) c₀ c₁ i
                     in isring +-AbGroup ·-Monoid is-dist

record IsCommRing {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
  constructor iscommring
  field
    is-Ring : [ isRing 0r 1r _+_ _·_ -_ ]
    ·-comm  : ∀ x y → x · y ≡ y · x

  open IsRing is-Ring public

  _ : [ isRing 0r 1r _+_ _·_ (-_) ]; _ = is-Ring
  _ : [ isCommutativeˢ _·_ is-set ]; _ = ·-comm

isCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) → hProp ℓ
isCommRing 0r 1r _+_ _·_ -_ .fst = IsCommRing 0r 1r _+_ _·_ -_
isCommRing 0r 1r _+_ _·_ -_ .snd (iscommring a₀ b₀) (iscommring a₁ b₁) = φ where
  abstract φ = λ i → let is-Ring = snd (isRing 0r 1r _+_ _·_ -_) a₀ a₁ i
                         is-set  = IsRing.is-set is-Ring
                         ·-comm  = snd (isCommutativeˢ _·_ is-set) b₀ b₁ i
                     in iscommring is-Ring ·-comm

-- Definition 4.1.2.
-- A classical field is a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

record IsClassicalField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ ! [ ¬'(x ≡ 0f) ] }} → F) : Type ℓ where
  constructor isclassicalfield

  field
    is-set      : [ isSetᵖ F ]
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
    -- WARNING: this is not directly Booij's definition, since Booij does not talk about an inverse operation `_⁻¹`
    --          we need to somehow obtain this operation
    ·-inv       : [ isNonzeroInverseˢ' is-set 0f 1f _·_ _⁻¹ ] -- classical version of `isNonzeroInverse`

  ·-linv : (x : F) {{ p : ! [ ¬' (x ≡ 0f) ] }} → ((x ⁻¹) · x) ≡ 1f -- wow, uses `p` already in `⁻¹`
  ·-linv x {{p}} = snd (·-inv x)

  ·-rinv : (x : F) {{ p : ! [ ¬' (x ≡ 0f) ] }} → (x · (x ⁻¹)) ≡ 1f
  ·-rinv x {{p}} = fst (·-inv x)

  open IsCommRing is-CommRing hiding (is-set) public

isClassicalField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ ! [ ¬'(x ≡ 0f) ] }} → F) → hProp ℓ
isClassicalField 0f 1f _+_ _·_ -_ _⁻¹ .fst = IsClassicalField 0f 1f _+_ _·_ -_ _⁻¹
isClassicalField 0f 1f _+_ _·_ -_ _⁻¹ .snd (isclassicalfield a₀ b₀ c₀) (isclassicalfield a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isclassicalfield is-set (snd (isCommRing 0f 1f _+_ _·_ -_) b₀ b₁ i) (snd (isNonzeroInverseˢ' is-set 0f 1f _·_ _⁻¹) c₀ c₁ i)

-- Definition 4.1.5.
-- A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. x : F has a multiplicative inverse iff x # 0;
-- 3. # is tight, i.e. ¬(x # y) ⇒ x = y;
-- 4. + is #-extensional, that is, for all w, x, y, z : F
--    w + x # y + z ⇒ w # y ∨ x # z.

record IsConstructiveField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_#_ : hPropRel F F ℓ') {- (_⁻¹ : (x : F) → {{[ x # 0f ]}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor isconstructivefield

  field
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
  open IsCommRing is-CommRing using (is-set)
  field
    ·-inv''     : ∀ x → [ (∃[ y ] [ is-set ] x · y ≡ˢ 1f) ⇔ x # 0f ]
    -- these should follow:
    --   ·-inv       : [ isNonzeroInverseˢ is-set 0f 1f _·_ _#_ _⁻¹ ]
    --   ·-invnz     : [ isInverseNonzeroˢ is-set 0f 1f _·_ _#_ ]
    --   ·-inv-back : ∀ x y → (x · y ≡ 1f) → [ x # 0f ] × [ y # 0f ]
    +-#-ext     : ∀ w x y z → [ (w + x) # (y + z) ] → [ (w # y) ⊔ (x # z) ]
    #-tight     : ∀ a b → [ ¬(a # b) ] → a ≡ b
    -- #-ApartnessRel  : [ isApartnessRel _#_ ]
  --
  -- ·-linv : (x : F) {{ p : [ x # 0f ] }} → ((x ⁻¹) · x) ≡ 1f -- wow, uses `p` already in `⁻¹`
  -- ·-linv x {{p}} = snd (·-inv x)
  --
  -- ·-rinv : (x : F) {{ p : [ x # 0f ] }} → (x · (x ⁻¹)) ≡ 1f
  -- ·-rinv x {{p}} = fst (·-inv x)

  _ : [ isCommRing 0f 1f _+_ _·_ -_              ]; _ = is-CommRing
  _ : [ isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_ ]; _ = ·-inv''
  _ : [ is-+-#-Extensional _+_ _#_               ]; _ = +-#-ext
  _ : [ isTightˢ''' _#_ is-set                   ]; _ = #-tight

  open IsCommRing is-CommRing hiding (is-set) public
  -- open IsApartnessRelᵖ isApartnessRel public
  --   renaming
  --     ( isIrrefl  to #-irrefl
  --     ; isSym     to #-sym
  --     ; isCotrans to #-cotrans )

isConstructiveField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_#_ : hPropRel F F ℓ') {- (_⁻¹ : (x : F) → {{[ x # 0f ]}} → F) -} → hProp (ℓ-max ℓ ℓ')
isConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -} .fst = IsConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -}
isConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -} .snd (isconstructivefield a₀ b₀ c₀ d₀) (isconstructivefield a₁ b₁ c₁ d₁) = φ where
  abstract φ = λ i → let is-CommRing = snd (isCommRing 0f 1f _+_ _·_ -_) a₀ a₁ i
                         is-set      = IsCommRing.is-set is-CommRing
                         in isconstructivefield is-CommRing (snd (isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_) b₀ b₁ i) (snd (is-+-#-Extensional _+_ _#_) c₀ c₁ i) (snd (isTightˢ''' _#_ is-set) d₀ d₁ i)

-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.

-- Remark 4.1.9.
--   1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that for every x and y,
--        max(x, y) = x ∨ max(x, y) = y,
--      which would hold in a linear order.
--      However, in Lemma 6.7.1 we characterize max as
--        z < max(x, y) ⇔ z < x ∨ z < y,
--     and similarly for min.
--   2. In a partial order, for two fixed elements a and b, all joins and meets of a, b are equal,
--      so that Lemma 2.6.20 the type of joins and the type of meets are propositions.
--      Hence, providing the maps min and max as in the above definition is equivalent to
--      the showing the existence of all binary joins and meets.

-- NOTE: in the non-cubical standard library, we have
--
--   record IsLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
--     field
--       ∨-comm        : Commutative ∨  -- ∀ x y     →                 (x ∨ y) ≈ (y ∨ x)
--       ∨-assoc       : Associative ∨  -- ∀ x y z   →                 ((x ∨ y) ∨ z) ≈ (x ∨ (y ∨ z))
--       ∨-cong        : Congruent₂ ∨   -- ∀ x y u v → x ≈ y → u ≈ v → (x ∨ u) ≈ (y ∨ v)
--       ∧-comm        : Commutative ∧  -- ∀ x y     →                 (x ∧ y) ≈ (y ∧ x)
--       ∧-assoc       : Associative ∧  -- ∀ x y z   →                 ((x ∧ y) ∧ z) ≈ (x ∧ (y ∧ z))
--       ∧-cong        : Congruent₂ ∧   -- ∀ x y u v → x ≈ y → u ≈ v → (x ∧ u) ≈ (y ∧ v)
--       absorptive    : Absorptive ∨ ∧ -- ∀ x y     →                 ((x ∨ (x ∧ y)) ≈ x) × ((x ∧ (x ∨ y)) ≈ x)
--
-- where they derive
--
--   ∨-absorbs-∧ : ∨ Absorbs ∧
--   ∨-absorbs-∧ = proj₁ absorptive
--
--   ∧-absorbs-∨ : ∧ Absorbs ∨
--   ∧-absorbs-∨ = proj₂ absorptive
--
--   ∧-congˡ : LeftCongruent ∧
--   ∧-congˡ y≈z = ∧-cong refl y≈z
--
--   ∧-congʳ : RightCongruent ∧
--   ∧-congʳ y≈z = ∧-cong y≈z refl
--
--   ∨-congˡ : LeftCongruent ∨
--   ∨-congˡ y≈z = ∨-cong refl y≈z
--
--   ∨-congʳ : RightCongruent ∨
--   ∨-congʳ y≈z = ∨-cong y≈z refl
--
-- and additionally we might also proof Lemma 6.7.1 and Lemma 2.6.20 (as mentioned in the remark above)
-- maybe we can proof from a linearorder that we have MinTrichtotomy and MaxTrichtotomy

record IsLattice {A : Type ℓ} (_≤_ : hPropRel A A ℓ') (min max : A → A → A) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    ≤-PartialOrder : [ isPartialOrder _≤_ ]
    is-min         : ∀ x y z → [ z ≤ (min x y) ⇔ z ≤ x ⊓ z ≤ y ]
    is-max         : ∀ x y z → [ (max x y) ≤ z ⇔ x ≤ z ⊓ y ≤ z ]
    -- glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
    -- glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
    -- lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
    -- lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z

  _ : [ isPartialOrder _≤_ ]; _ = ≤-PartialOrder
  _ : [ isMin _≤_ min      ]; _ = is-min
  _ : [ isMax _≤_ max      ]; _ = is-max

  open IsPartialOrder ≤-PartialOrder public
    renaming
      ( is-refl    to ≤-refl
      ; is-antisym to ≤-antisym
      ; is-trans   to ≤-trans )

isLattice : {A : Type ℓ} (_≤_ : hPropRel A A ℓ') (min max : A → A → A) → hProp (ℓ-max ℓ ℓ')
isLattice _≤_ min max .fst = IsLattice _≤_ min max
isLattice _≤_ min max .snd (islattice a₀ b₀ c₀) (islattice a₁ b₁ c₁) = φ where
  abstract φ = λ i → islattice (snd (isPartialOrder _≤_) a₀ a₁ i) (snd (isMin _≤_ min) b₀ b₁ i) (snd (isMax _≤_ max) c₀ c₁ i)

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

record IsAlmostPartiallyOrderedField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor isalmostpartiallyorderedfield

  infixl 4 _#_
  infixl 4 _≤_

  -- ≤, as in Lemma 4.1.7
  _≤_ : hPropRel F F ℓ'
  x ≤ y = ¬ (y < x)

  field
    -- 1.
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
    -- 2.
    <-StrictPartialOrder : [ isStrictPartialOrder _<_ ]

  open IsCommRing is-CommRing public
  open IsStrictPartialOrder <-StrictPartialOrder public
    renaming
      ( is-irrefl  to <-irrefl
      ; is-trans   to <-trans
      ; is-cotrans to <-cotrans )

  <-asym : [ isAsym _<_ ]
  <-asym = irrefl+trans⇒asym _<_ <-irrefl <-trans

  -- # is defined as in Lemma 4.1.7
  _#_ : hPropRel F F ℓ'
  x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  field
    -- 3.
    ·-inv''     : ∀ x → [ (∃[ y ] [ is-set ] x · y ≡ˢ 1f) ⇔ x # 0f ]
    -- ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    -- ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    -- ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    -- 4. NOTE: we already have ≤-isPartialOrder in ≤-isLattice
    -- ≤-isPartialOrder : IsPartialOrder _≤_
    -- 5.
    ≤-Lattice : [ isLattice _≤_ min max ]

  _ : isSet F                                     ; _ = is-set
  _ : [ isCommRing 0f 1f _+_ _·_ (-_)            ]; _ = is-CommRing
  _ : [ isStrictPartialOrder _<_                 ]; _ = <-StrictPartialOrder
  _ : [ isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_ ]; _ = ·-inv''
  _ : [ isLattice _≤_ min max                    ]; _ = ≤-Lattice

  open IsLattice ≤-Lattice renaming (≤-antisym to ≤-antisymᵗ) public

  ≤-antisym : [ isAntisymˢ _≤_ is-set ]
  ≤-antisym = isAntisymˢ⇔isAntisym _≤_ is-set .snd ≤-antisymᵗ

isAlmostPartiallyOrderedField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} → hProp (ℓ-max ℓ ℓ')
isAlmostPartiallyOrderedField {ℓ = ℓ} {ℓ' = ℓ'} {F = F} 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .fst = IsAlmostPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -}
isAlmostPartiallyOrderedField {ℓ = ℓ} {ℓ' = ℓ'} {F = F} 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .snd (isalmostpartiallyorderedfield a₀ b₀ c₀ d₀) (isalmostpartiallyorderedfield a₁ b₁ c₁ d₁) = φ where
  abstract φ = λ i → let -- we are doing basically "the same" as in `IsAlmostPartiallyOrderedField`
                         _≤_                  : hPropRel F F ℓ'
                         x ≤ y                = ¬ (y < x) -- ≤, as in Lemma 4.1.7
                         is-CommRing          = snd (isCommRing 0f 1f _+_ _·_ -_) a₀ a₁ i
                         is-set               = IsCommRing.is-set is-CommRing
                         <-StrictPartialOrder = snd (isStrictPartialOrder _<_) b₀ b₁ i
                         open IsStrictPartialOrder <-StrictPartialOrder
                           renaming
                             ( is-irrefl  to <-irrefl
                             ; is-trans   to <-trans
                             ; is-cotrans to <-cotrans )
                         <-asym               : [ isAsym _<_ ]
                         <-asym               = irrefl+trans⇒asym _<_ <-irrefl <-trans
                         _#_                  : hPropRel F F ℓ'
                         x # y                = [ <-asym x y ] (x < y) ⊎ᵖ (y < x) -- # is defined as in Lemma 4.1.7
                         ·-inv''              = snd (isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_) c₀ c₁ i
                         ≤-isLattice          = snd (isLattice _≤_ min max) d₀ d₁ i
                     in isalmostpartiallyorderedfield is-CommRing <-StrictPartialOrder ·-inv'' ≤-isLattice

record IsPartiallyOrderedField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor ispartiallyorderedfield
  field
    -- 1. 2. 3. 4. 5.
    is-AlmostPartiallyOrderedField : [ isAlmostPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ᶠ -} ]
    -- 6. (†)
    +-<-ext : ∀ w x y z → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
    -- 6. (∗)
    ·-preserves-< : ∀ x y z → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]

  _ : [ isAlmostPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max ]; _ = is-AlmostPartiallyOrderedField
  _ : [ is-+-<-Extensional _+_ _<_                                 ]; _ = +-<-ext
  _ : [ operation _·_ preserves _<_ when (λ z → 0f < z)            ]; _ = ·-preserves-<

  open IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public

isPartiallyOrderedField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} → hProp (ℓ-max ℓ ℓ')
isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .fst = IsPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -}
isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .snd (ispartiallyorderedfield a₀ b₀ c₀) (ispartiallyorderedfield a₁ b₁ c₁) = φ where
  abstract φ = λ i → ispartiallyorderedfield (snd (isAlmostPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ᶠ -}) a₀ a₁ i) (snd (is-+-<-Extensional _+_ _<_) b₀ b₁ i) (snd (operation _·_ preserves _<_ when (λ z → 0f < z)) c₀ c₁ i)
