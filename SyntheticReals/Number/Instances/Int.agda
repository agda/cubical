{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Instances.Int where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation --.Properties

open import SyntheticReals.Utils using (!_; !!_)
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.MorePropAlgebra.Bundles
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.Number.Structures2
open import SyntheticReals.Number.Bundles2

open import SyntheticReals.Number.Instances.Nat using (lemma10''; lemma12'')
open import SyntheticReals.Number.Prelude.Nat

import Agda.Builtin.Int as Builtin
import Data.Integer.Base as BuiltinBase
import Data.Integer.Properties as BuiltinProps

open import Cubical.Data.Int renaming
  ( Int to ℤ
  ; isSetInt to isSetℤ
  ; _-_ to infix 7 _-_
  ; _+_ to infix 5 _+_
  )

import Cubical.HITs.Ints.QuoInt as QuoInt

-- Cubical.Data.Int is isomorphic to Agda.Builtin.Int
Int≅Builtin : Iso ℤ Builtin.Int
Int≅Builtin .Iso.fun      (        pos    n) = Builtin.pos n
Int≅Builtin .Iso.fun      (        negsuc n) = Builtin.negsuc n
Int≅Builtin .Iso.inv      (Builtin.pos    n) = pos n
Int≅Builtin .Iso.inv      (Builtin.negsuc n) = negsuc n
Int≅Builtin .Iso.rightInv (Builtin.pos    n) = refl
Int≅Builtin .Iso.rightInv (Builtin.negsuc n) = refl
Int≅Builtin .Iso.leftInv  (        pos    n) = refl
Int≅Builtin .Iso.leftInv  (        negsuc n) = refl

Int≡Builtin : ℤ ≡ Builtin.Int
Int≡Builtin = isoToPath Int≅Builtin

Sign : Type₀
Sign = Bool

pattern spos = Bool.false
pattern sneg = Bool.true

_·ˢ_ : Sign → Sign → Sign
_·ˢ_ = Bool._⊕_

sign : ℤ → Sign
sign (pos n)    = spos
sign (negsuc n) = sneg

signed : Sign → ℕ → ℤ
signed spos      x  = pos x
signed sneg  zero   = 0
signed sneg (suc x) = neg (suc x)

-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

-involutive : ∀ a → - - a ≡ a
-involutive (pos zero) = refl
-involutive (pos (suc n)) = refl
-involutive (negsuc n) = refl

infix 8 -_
infix 7 _·_
infix 7 _·'_
infix 7 _·''_
infixl 4 _<_

-- multiplication on integers
-- NOTE: this definition leads to a lot cases and a lot of calculations
--       the general advice would be to have as few cases as possible
--       because then at a call site we also need not many cases
-- NOTE: the way that QuoInt._+_ is defined works that it reduces the first argument, e.g. it reduces `a` in `a + b`
--       therefore we also need to split (only) on the first argument `a`
--         _+_ : ℤ → ℤ → ℤ
--         (signed _ zero) + n = n
--         (posneg _)      + n = n
--         (pos (suc m))   + n = sucℤ  (pos m + n)
--         (neg (suc m))   + n = predℤ (neg m + n)
--       we might apply something similar for _·_
--       although that is not done for QuoInt._*_
--         _*_ : ℤ → ℤ → ℤ
--         m * n = signed (sign m *S sign n) (abs m ℕ.* abs n)
--       but it is done for ℕ._*_
--         _*_ : Nat → Nat → Nat
--         zero  * m = zero
--         suc n * m = m + n * m
_·_ : ℤ → ℤ → ℤ
pos      a  · pos      b  = pos (a ·ⁿ b)
pos  zero   · negsuc   b  = pos 0
pos (suc a) · negsuc   b  = negsuc (a ·ⁿ b +ⁿ (a +ⁿ b)) -- maybe `(a +ⁿ b) +ⁿ a ·ⁿ b` would be a better choice ?
negsuc   a  · pos  zero   = pos 0
negsuc   a  · pos (suc b) = negsuc (a ·ⁿ b +ⁿ (a +ⁿ b))
negsuc   a  · negsuc   b  = pos (suc a ·ⁿ suc b)

-- an equivalent multiplication on integers
-- NOTE: this is the way it's defined in the noncubical standard library
--       I used it to proof associativity, which seemed incredibly hard for the previous definition
_·'_ : ℤ → ℤ → ℤ
x ·' y  = signed (sign x ·ˢ sign y) (abs x ·ⁿ abs y)

mksigned : Sign → ℕ → ℤ
mksigned s zero = pos 0
mksigned s (suc n) = signed s (suc n)

-- a third multiplication on the integers
-- NOTE: with the use of `mksigned` we need not case-split on the sign, if the absolute value is zero
_·''_ : ℤ → ℤ → ℤ
x ·'' y = mksigned (sign x ·ˢ sign y) (abs x ·ⁿ abs y)

abstract
  ·''-nullifiesʳ : ∀ x → x ·'' 0 ≡ 0
  ·''-nullifiesʳ (pos    n) i = mksigned spos (·ⁿ-nullifiesʳ n i)
  ·''-nullifiesʳ (negsuc n) i = mksigned sneg (·ⁿ-nullifiesʳ n i)

-- hProp-valued _<_
_<_ : ∀(x y : ℤ) → hProp ℓ-zero
pos    x < pos    y = x <ⁿ y
pos    x < negsuc y = ⊥
negsuc x < pos    y = ⊤
negsuc x < negsuc y = y <ⁿ x

min : ℤ → ℤ → ℤ
min (pos    x) (pos    y) = pos (minⁿ x y)
min (pos    x) (negsuc y) = negsuc y
min (negsuc x) (pos    y) = negsuc x
min (negsuc x) (negsuc y) = negsuc (maxⁿ x y)

max : ℤ → ℤ → ℤ
max (pos    x) (pos    y) = pos (maxⁿ x y)
max (pos    x) (negsuc y) = pos x
max (negsuc x) (pos    y) = pos y
max (negsuc x) (negsuc y) = negsuc (minⁿ x y)

-- some calculations that arose in the proofs
private
  abstract
    lemma1 : ∀ a b → a ·ⁿ b +ⁿ (a +ⁿ b) ≡ b +ⁿ a ·ⁿ suc b
    lemma1 a b = a ·ⁿ b +ⁿ (a +ⁿ b)  ≡⟨ (λ i → +ⁿ-assoc (a ·ⁿ b) a b i) ⟩
                (a ·ⁿ b +ⁿ a) +ⁿ b  ≡⟨ (λ i → +ⁿ-comm (a ·ⁿ b) a i +ⁿ b) ⟩
                (a +ⁿ a ·ⁿ b) +ⁿ b  ≡⟨ (λ i → +ⁿ-comm (a +ⁿ a ·ⁿ b) b i) ⟩
                b +ⁿ (a +ⁿ a ·ⁿ b)  ≡⟨ (λ i → b +ⁿ ·ⁿ-suc a b (~ i)) ⟩
                b +ⁿ a ·ⁿ suc b     ∎

    lemma2 : ∀ a b c →  c +ⁿ (b +ⁿ a ·ⁿ suc b) ·ⁿ suc c
                     ≡ (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ suc (c +ⁿ b ·ⁿ suc c)
    lemma2 a b c =
      c +ⁿ (b +ⁿ a ·ⁿ suc b) ·ⁿ suc c                 ≡⟨ (λ i → c +ⁿ ·ⁿ-distribʳ b (a ·ⁿ suc b) (suc c) (~ i)) ⟩
      c +ⁿ (b ·ⁿ suc c +ⁿ (a ·ⁿ suc b) ·ⁿ suc c)      ≡⟨ +ⁿ-assoc c _ _ ⟩
      (c +ⁿ b ·ⁿ suc c) +ⁿ (a ·ⁿ suc b) ·ⁿ suc c      ≡⟨ (λ i → (c +ⁿ b ·ⁿ suc c) +ⁿ ·ⁿ-assoc a (suc b) (suc c) (~ i)) ⟩
      (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ (suc b ·ⁿ suc c)      ≡⟨ refl ⟩
      (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ suc (c +ⁿ b ·ⁿ suc c) ∎

    lemma3 : ∀ y z → y ·ⁿ z +ⁿ (y +ⁿ z) ≡ y ·ⁿ suc z +ⁿ z
    lemma3 y z =     y ·ⁿ z +ⁿ (y +ⁿ z) ≡⟨ +ⁿ-assoc (y ·ⁿ z) y z ⟩
                   (y ·ⁿ z +ⁿ y) +ⁿ z  ≡⟨ (λ i → +ⁿ-comm (y ·ⁿ z) y i +ⁿ z) ⟩
                   (y +ⁿ y ·ⁿ z) +ⁿ z  ≡⟨ (λ i → ·ⁿ-suc y z (~ i) +ⁿ z) ⟩
                    y ·ⁿ suc z +ⁿ z    ∎

    lemma4 = λ(a b : ℕ) →
      a ·ⁿ suc b +ⁿ (a +ⁿ suc b)    ≡⟨ (λ i → ·ⁿ-suc a b i +ⁿ (a +ⁿ suc b)) ⟩
      (a +ⁿ a ·ⁿ b) +ⁿ (a +ⁿ suc b) ≡⟨ sym $ +ⁿ-assoc a (a ·ⁿ b) (a +ⁿ suc b) ⟩
      a +ⁿ (a ·ⁿ b +ⁿ (a +ⁿ suc b)) ≡⟨ (λ i → a +ⁿ +ⁿ-assoc (a ·ⁿ b) a (suc b) i) ⟩
      a +ⁿ ((a ·ⁿ b +ⁿ a) +ⁿ suc b) ≡⟨ (λ i → a +ⁿ +ⁿ-suc (a ·ⁿ b +ⁿ a) b i) ⟩
      a +ⁿ suc ((a ·ⁿ b +ⁿ a) +ⁿ b) ≡⟨ (λ i → a +ⁿ suc (+ⁿ-assoc (a ·ⁿ b) a b (~ i))) ⟩
      a +ⁿ suc (a ·ⁿ b +ⁿ (a +ⁿ b)) ∎

    lemma5 = λ(a b : ℕ) →
              a +ⁿ (b +ⁿ a ·ⁿ suc b) ≡⟨ +ⁿ-assoc a b (a ·ⁿ suc b) ⟩
              (a +ⁿ b) +ⁿ a ·ⁿ suc b ≡⟨ (λ i → +ⁿ-comm a b i +ⁿ a ·ⁿ suc b) ⟩
              (b +ⁿ a) +ⁿ a ·ⁿ suc b ≡⟨ sym $ +ⁿ-assoc b a (a ·ⁿ suc b) ⟩
              b +ⁿ (a +ⁿ a ·ⁿ suc b) ≡⟨ (λ i → b +ⁿ ·ⁿ-suc a (suc b) (~ i)) ⟩
              b +ⁿ a ·ⁿ suc (suc b)  ∎

    lemma6 : ∀ m n → suc (m +ⁿ n ·ⁿ suc (suc (suc m))) ≡ suc n +ⁿ (m +ⁿ n ·ⁿ suc (suc m))
    lemma6 m n = suc (m +ⁿ n ·ⁿ suc (suc (suc m)))  ≡⟨ (λ i → suc $ m +ⁿ ·ⁿ-suc n (suc (suc m)) i) ⟩
              suc (m +ⁿ (n +ⁿ n ·ⁿ suc (suc m))) ≡⟨ (λ i → suc $ +ⁿ-assoc m n (n ·ⁿ (suc (suc m))) i) ⟩
              suc ((m +ⁿ n) +ⁿ n ·ⁿ suc (suc m)) ≡⟨ (λ i → suc $ +ⁿ-comm m n i +ⁿ n ·ⁿ suc (suc m)) ⟩
              suc ((n +ⁿ m) +ⁿ n ·ⁿ suc (suc m)) ≡⟨ (λ i → suc $ +ⁿ-assoc n m (n ·ⁿ (suc (suc m))) (~ i)) ⟩
              suc (n +ⁿ (m +ⁿ n ·ⁿ suc (suc m))) ≡⟨ refl ⟩
              suc n +ⁿ (m +ⁿ n ·ⁿ suc (suc m))   ∎

    lemma7 : ∀ a b → b +ⁿ a ·ⁿ suc b ≡ a +ⁿ b ·ⁿ suc a
    lemma7 a b =
      b +ⁿ a ·ⁿ suc b    ≡⟨ (λ i → b +ⁿ ·ⁿ-suc a b i) ⟩
      b +ⁿ (a +ⁿ a ·ⁿ b) ≡⟨ (λ i → +ⁿ-assoc b a (a ·ⁿ b) i) ⟩
      (b +ⁿ a) +ⁿ a ·ⁿ b ≡⟨ (λ i → +ⁿ-comm b a i +ⁿ a ·ⁿ b) ⟩
      (a +ⁿ b) +ⁿ a ·ⁿ b ≡⟨ (λ i → +ⁿ-assoc a b (a ·ⁿ b) (~ i)) ⟩
      a +ⁿ (b +ⁿ a ·ⁿ b) ≡⟨ (λ i → a +ⁿ (b +ⁿ ·ⁿ-comm a b i)) ⟩
      a +ⁿ (b +ⁿ b ·ⁿ a) ≡⟨ (λ i → a +ⁿ ·ⁿ-suc b a (~ i)) ⟩
      a +ⁿ b ·ⁿ suc a    ∎

abstract
  <-irrefl : (a : ℤ) → [ ¬ (a < a) ]
  <-irrefl (pos  zero  ) = <ⁿ-irrefl 0
  <-irrefl (pos (suc n)) = <ⁿ-irrefl (suc n)
  <-irrefl (negsuc   n ) = <ⁿ-irrefl n

  <-trans : (a b c : ℤ) → [ a < b ] → [ b < c ] → [ a < c ]
  <-trans (pos    a) (pos    b) (pos    c) a<b b<c = <ⁿ-trans a<b b<c
  <-trans (negsuc a) (pos    b) (pos    c) a<b b<c = tt
  <-trans (negsuc a) (negsuc b) (pos    c) a<b b<c = tt
  <-trans (negsuc a) (negsuc b) (negsuc c) a<b b<c = <ⁿ-trans b<c a<b

  <-asym : (a b : ℤ) → [ a < b ] → [ ¬(b < a) ]
  <-asym = irrefl+trans⇒asym _<_ <-irrefl <-trans

  <-cotrans : (a b : ℤ) → [ a < b ] → (x : ℤ) → [ (a < x) ⊔ (x < b) ]
  <-cotrans (pos    a) (pos    b) a<b (pos    x) = <ⁿ-cotrans _ _ a<b x
  <-cotrans (pos    a) (pos    b) a<b (negsuc x) = inrᵖ tt
  <-cotrans (negsuc a) (pos    b) a<b (pos    x) = inlᵖ tt
  <-cotrans (negsuc a) (pos    b) a<b (negsuc x) = inrᵖ tt
  <-cotrans (negsuc a) (negsuc b) a<b (pos    x) = inlᵖ tt
  <-cotrans (negsuc a) (negsuc b) a<b (negsuc x) = pathTo⇒ (⊔-comm (b <ⁿ x) (x <ⁿ a)) (<ⁿ-cotrans _ _ a<b x)

-- some properties about `pos`, `negsuc`, `+pos` and `+negsuc`
abstract
  +-identityʳ : ∀ x → x + 0 ≡ x
  +-identityʳ x = refl

  +-identityˡ : ∀ x → 0 + x ≡ x
  +-identityˡ x = +-comm 0 x ∙ +-identityʳ x

  -- usage count: 3
  -1·≡- : ∀ a → negsuc 0 · a ≡ - a
  -1·≡- (pos zero) = refl
  -1·≡- (pos (suc n)) = refl
  -1·≡- (negsuc n) = λ i → pos $ suc $ +ⁿ-comm n 0 i

  -- usage count: 0
  negsuc≡-pos : ∀ a → negsuc a ≡ - pos (suc a)
  negsuc≡-pos a = refl

  -- usage count: 2
  negsuc-reflects-≡ : ∀ x y → negsuc x ≡ negsuc y → x ≡ y
  negsuc-reflects-≡ x y p i = predⁿ (abs (p i))

  -- usage count: 2
  pos-reflects-≡ : ∀ x y → pos x ≡ pos y → x ≡ y
  pos-reflects-≡ x y p i = abs (p i)

  -- usage count: 1 - 2
  possuc+negsuc≡0 : ∀ n → (pos (suc n) +negsuc n) ≡ pos 0
  possuc+negsuc≡0 zero = refl
  possuc+negsuc≡0 (suc n) = let r = possuc+negsuc≡0 n in sym ind ∙ r where
    ind =           pos      (suc n)   +negsuc n  ≡⟨ refl ⟩
           predInt (pos (suc (suc n))) +negsuc n  ≡⟨ sym $ predInt+negsuc n (pos (suc (suc n))) ⟩
           predInt (pos (suc (suc n))  +negsuc n) ∎

  -- usage count: 0 - 1
  sucInt[negsuc+pos]≡0 : ∀ n → sucInt (negsuc n +pos n) ≡ pos 0
  sucInt[negsuc+pos]≡0 zero = refl
  sucInt[negsuc+pos]≡0 (suc n) = let r = sucInt[negsuc+pos]≡0 n in sym ind ∙ r where
    ind = sucInt (        negsuc n        +pos n ) ≡⟨ refl ⟩
          sucInt (sucInt (negsuc (suc n)) +pos n ) ≡⟨ (λ i → sucInt $ sucInt+pos n (negsuc (suc n)) (~ i)) ⟩
          sucInt (sucInt (negsuc (suc n)  +pos n)) ∎

  +-inverseʳ : ∀ a → a + (- a) ≡ 0
  +-inverseʳ (pos  zero  ) = refl
  +-inverseʳ (pos (suc n)) = possuc+negsuc≡0 n
  +-inverseʳ (negsuc   n ) = sucInt[negsuc+pos]≡0 n

  +-inverseˡ : ∀ a → (- a) + a ≡ 0
  +-inverseˡ a = +-comm (- a) a ∙ +-inverseʳ a

  +-inverse : (x : ℤ) → (x + (- x) ≡ pos 0) × ((- x) + x ≡ pos 0)
  +-inverse x .fst = +-inverseʳ x
  +-inverse x .snd = +-inverseˡ x

  -- usage count: 11 - 14
  pos+pos≡+ⁿ : ∀ a x → (pos a +pos x) ≡ pos (a +ⁿ x)
  pos+pos≡+ⁿ a zero = λ i → pos $ +ⁿ-comm 0 a i
  pos+pos≡+ⁿ a (suc x) = let r = pos+pos≡+ⁿ a x in
    sucInt (pos a +pos x) ≡⟨ (λ i → sucInt $ r i) ⟩
    sucInt (pos (a +ⁿ x)) ≡⟨ refl ⟩
    pos (suc (a +ⁿ x))    ≡⟨ (λ i → pos $ +ⁿ-suc a x (~ i)) ⟩
    pos (a +ⁿ suc x)      ∎

  -- usage count: 7 - 8
  negsuc+negsuc≡+ⁿ : ∀ a x → (negsuc a +negsuc x) ≡ negsuc (suc (a +ⁿ x))
  negsuc+negsuc≡+ⁿ a zero = λ i → negsuc $ suc $ +ⁿ-comm 0 a i
  negsuc+negsuc≡+ⁿ a (suc x) = let r = negsuc+negsuc≡+ⁿ a x in
    predInt (negsuc a +negsuc x)    ≡⟨ (λ i → predInt (r i)) ⟩
    predInt (negsuc (suc (a +ⁿ x))) ≡⟨ refl ⟩
    negsuc (suc (suc (a +ⁿ x)))     ≡⟨ (λ i → negsuc $ suc $ +ⁿ-suc a x (~ i)) ⟩
    negsuc (suc (a +ⁿ suc x))       ∎

  -- usage count: 6 - 7
  +negsuc-identityˡ : ∀ x → 0 +negsuc x ≡ negsuc x
  +negsuc-identityˡ zero = refl
  +negsuc-identityˡ (suc x) = λ i → predInt $ +negsuc-identityˡ x i

  -- usage count: 0
  pos+negsuc≡⊎ : ∀ a b → (Σ[ y ∈ ℕ ] pos a +negsuc b ≡ pos y) ⊎ (Σ[ y ∈ ℕ ] pos a +negsuc b ≡ negsuc y)
  pos+negsuc≡⊎ zero zero = inr (0 , refl)
  pos+negsuc≡⊎ (suc a) zero = inl (a , refl)
  pos+negsuc≡⊎ zero (suc b) = inr (suc b , λ i → predInt $ +negsuc-identityˡ b i)
  pos+negsuc≡⊎ (suc a) (suc b) with pos+negsuc≡⊎ a b
  ... | inl (y , p) = inl (y , predInt+negsuc b (pos (suc a)) ∙ p)
  ... | inr (y , p) = inr (y , predInt+negsuc b (pos (suc a)) ∙ p)

  -- usage count: 0
  negsuc+pos≡⊎ : ∀ a b → (Σ[ y ∈ ℕ ] negsuc a +pos b ≡ pos y) ⊎ (Σ[ y ∈ ℕ ] negsuc a +pos b ≡ negsuc y)
  negsuc+pos≡⊎ zero zero = inr (0 , refl)
  negsuc+pos≡⊎ (suc a) zero = inr (suc a , refl)
  negsuc+pos≡⊎ zero (suc b) = inl (b , sucInt+pos b (negsuc 0) ∙ +-identityˡ (pos b))
  negsuc+pos≡⊎ (suc a) (suc b) with negsuc+pos≡⊎ a b
  ... | inl (y , p) = inl (y , sucInt+pos b (negsuc (suc a)) ∙ p)
  ... | inr (y , p) = inr (y , sucInt+pos b (negsuc (suc a)) ∙ p)

  -- usage count: 4 - 6
  pos+negsuc≡negsuc+pos : ∀ a b → pos a +negsuc b ≡ negsuc b +pos a
  pos+negsuc≡negsuc+pos a zero = (λ i → predInt $ pos+pos≡+ⁿ 0 a (~ i)) ∙ predInt+pos a 0
  pos+negsuc≡negsuc+pos a (suc b) = (λ i → predInt $ pos+negsuc≡negsuc+pos a b i) ∙ predInt+ (negsuc b) (pos a)

  -- usage count: 0 - 1
  predInt- : ∀ a → predInt (- a) ≡ - (sucInt a)
  predInt- (pos zero) = refl
  predInt- (pos (suc n)) = refl
  predInt- (negsuc zero) = refl
  predInt- (negsuc (suc n)) = refl

  -- usage count: 2 - 3
  pos+negsuc-swap : ∀ a b → pos (suc a) +negsuc b ≡ -(pos (suc b) + negsuc a)
  pos+negsuc-swap zero zero = refl
  pos+negsuc-swap (suc a) zero = λ i → - (predInt+negsuc a 1 ∙ +negsuc-identityˡ a) (~ i)
  pos+negsuc-swap a (suc b) =
    predInt (pos (suc a) +negsuc b)     ≡⟨ (λ i → predInt $ pos+negsuc-swap a b i) ⟩
    predInt (- (pos (suc b) +negsuc a)) ≡⟨ predInt- (pos (suc b) +negsuc a) ⟩
    - sucInt (pos (suc b) +negsuc a)    ≡⟨ (λ i → - sucInt+negsuc a (pos (suc b)) i) ⟩
    - (pos (suc (suc b)) +negsuc a)     ∎

  -- usage count: 2
  negsuc+pos-swap : ∀ a b → negsuc a +pos (suc b) ≡ -(negsuc b + pos (suc a))
  negsuc+pos-swap a b = sym (pos+negsuc≡negsuc+pos (suc b) a) ∙ pos+negsuc-swap b a ∙ (λ i → - pos+negsuc≡negsuc+pos (suc a) b i)

  -- usage count: 1
  +negsuc-assoc : ∀ a b c → a +negsuc (b +ⁿ suc c) ≡ (a +negsuc b) +negsuc c
  +negsuc-assoc a b c = (λ i → a + (negsuc+negsuc≡+ⁿ b c ∙ (λ j → negsuc (+ⁿ-suc b c (~ j)))) (~ i)) ∙ +-assoc a (negsuc b) (negsuc c)

  -- usage count: 1
  sucInt[negsuc+pos]≡pos : ∀ a → sucInt (negsuc 0 +pos a) ≡ pos a
  sucInt[negsuc+pos]≡pos a = sucInt+pos a (negsuc 0) ∙ pos+pos≡+ⁿ 0 a

  -- usage count: 1
  +pos-inverse : ∀ a → negsuc a +pos a ≡ negsuc 0
  +pos-inverse zero = refl
  +pos-inverse (suc a) = sucInt+pos a (negsuc (suc a)) ∙ +pos-inverse a

  -- usage count: 1
  +pos-assoc : ∀ a b c → (a +pos b) +pos c ≡ a +pos (b +ⁿ c)
  +pos-assoc a b c = sym (+-assoc a (pos b) (pos c)) ∙ (λ i → a + pos+pos≡+ⁿ b c i)

data Trichotomy (m n : ℤ) : Type₀ where
  lt : [ m < n ] → Trichotomy m n
  eq :   m ≡ n   → Trichotomy m n
  gt : [ n < m ] → Trichotomy m n

_≟_ : ∀ m n → Trichotomy m n
pos    a ≟ pos    b with a ≟ⁿ b
... | ltⁿ p = lt p
... | eqⁿ p = eq λ i → pos (p i)
... | gtⁿ p = gt p
pos    a ≟ negsuc b = gt tt
negsuc a ≟ pos    b = lt tt
negsuc a ≟ negsuc b with a ≟ⁿ b
... | ltⁿ p = gt p
... | eqⁿ p = eq λ i → negsuc (p i)
... | gtⁿ p = lt p

data MinTrichtotomy (x y : ℤ) : Type where
  min-lt : min x y ≡ x → [ x < y ]   → MinTrichtotomy x y
  min-gt : min x y ≡ y → [ y < x ]   → MinTrichtotomy x y
  min-eq : min x y ≡ x → min x y ≡ y → MinTrichtotomy x y

data MaxTrichtotomy (x y : ℤ) : Type where
  max-lt : max x y ≡ y → [ x < y ]   → MaxTrichtotomy x y
  max-gt : max x y ≡ x → [ y < x ]   → MaxTrichtotomy x y
  max-eq : max x y ≡ x → max x y ≡ y → MaxTrichtotomy x y

min-trichotomy : ∀ x y → MinTrichtotomy x y
min-trichotomy (pos    x) (pos    y) with (pos x) ≟ (pos y)
... | lt p = min-lt (λ i → pos $ minⁿ-tightˡ x y p i) p
... | eq p = let minxy≡x = (λ i → minⁿ x (pos-reflects-≡ x y p (~ i))) ∙ minⁿ-identity x
             in min-eq (λ j → pos $ minxy≡x j) ((λ i → pos $ minxy≡x i) ∙ p)
... | gt p = min-gt (λ i → pos $ minⁿ-tightʳ x y p i) p
min-trichotomy (pos    x) (negsuc y) = min-gt refl tt
min-trichotomy (negsuc x) (pos    y) = min-lt refl tt
min-trichotomy (negsuc x) (negsuc y) with (negsuc x) ≟ (negsuc y)
... | lt p = min-lt (λ i → negsuc $ maxⁿ-tightˡ x y p i) p
... | eq p = let maxxy≡x = (λ i → maxⁿ x (negsuc-reflects-≡ x y p (~ i))) ∙ maxⁿ-identity x
             in min-eq (λ j → negsuc $ maxxy≡x j) ((λ i → negsuc $ maxxy≡x i) ∙ p)
... | gt p = min-gt (λ i → negsuc $ maxⁿ-tightʳ x y p i) p

max-trichotomy : ∀ x y → MaxTrichtotomy x y
max-trichotomy (pos    x) (pos    y) with (pos x) ≟ (pos y)
... | lt p = max-lt ((λ i → pos $ maxⁿ-tightʳ x y p i)) p
... | eq p = let maxxy≡x = (λ i → maxⁿ x (pos-reflects-≡ x y p (~ i))) ∙ maxⁿ-identity x
             in max-eq (λ j → pos $ maxxy≡x j) ((λ i → pos $ maxxy≡x i) ∙ p)
... | gt p = max-gt (λ i → pos $ maxⁿ-tightˡ x y p i) p
max-trichotomy (pos    x) (negsuc y) = max-gt refl tt
max-trichotomy (negsuc x) (pos    y) = max-lt refl tt
max-trichotomy (negsuc x) (negsuc y) with (negsuc x) ≟ (negsuc y)
... | lt p = max-lt (λ i → negsuc $ minⁿ-tightʳ x y p i) p
... | eq p = let minxy≡x = (λ i → minⁿ x (negsuc-reflects-≡ x y p (~ i))) ∙ minⁿ-identity x
             in max-eq (λ j → negsuc $ minxy≡x j) ((λ i → negsuc $ minxy≡x i) ∙ p)
... | gt p = max-gt (λ i → negsuc $ minⁿ-tightˡ x y p i) p

abstract
  -- NOTE: same proof as in `Number.Instances.Nat`
  is-min : (x y z : ℤ) → [ ¬ᵖ (min x y < z) ⇔ ¬ᵖ (x < z) ⊓ ¬ᵖ (y < z) ]
  is-min x y z .fst z≤minxy with min-trichotomy x y
  ... | min-lt p x<y = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → p i < z) $ <-trans x y z x<y y<z)
  ... | min-gt p y<x = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) $ <-trans y x z y<x x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → p i < z) y<z)
  ... | min-eq p q   = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → q i < z) y<z)
  is-min x y z .snd (z≤x , z≤y) minxy<z with min-trichotomy x y
  ... | min-lt p _   = z≤x $ pathTo⇒ (λ i → p i < z) minxy<z
  ... | min-gt p _   = z≤y $ pathTo⇒ (λ i → p i < z) minxy<z
  ... | min-eq p q   = z≤x $ pathTo⇒ (λ i → p i < z) minxy<z

  -- NOTE: same proof as in `Number.Instances.Nat`
  is-max : (x y z : ℤ) → [ ¬ᵖ (z < max x y) ⇔ ¬ᵖ (z < x) ⊓ ¬ᵖ (z < y) ]
  is-max x y z .fst maxxy≤z with max-trichotomy x y
  ... | max-gt p y<x = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<x )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < p i) $ <-trans z y x z<y y<x )
  ... | max-lt p x<y = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) $ <-trans z x y z<x x<y )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<y )
  ... | max-eq p q   = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<x )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < q i) z<y )
  is-max x y z .snd (z≤x , z≤y) maxxy<z with max-trichotomy x y
  ... | max-gt p _   = z≤x $ pathTo⇒ (λ i → z < p i) maxxy<z
  ... | max-lt p _   = z≤y $ pathTo⇒ (λ i → z < p i) maxxy<z
  ... | max-eq p q   = z≤x $ pathTo⇒ (λ i → z < p i) maxxy<z

abstract
  sucInt-reflects-< : ∀ x y → [ sucInt x < sucInt y ] → [ x < y ]
  sucInt-reflects-< (pos         x ) (pos         y ) p = sucⁿ-creates-<ⁿ x y .snd p
  sucInt-reflects-< (pos         x ) (negsuc  zero  ) p = ¬-<ⁿ-zero p
  sucInt-reflects-< (negsuc      x ) (pos         y ) p = tt
  sucInt-reflects-< (negsuc  zero  ) (negsuc  zero  ) p = p
  sucInt-reflects-< (negsuc (suc x)) (negsuc  zero  ) p = 0<ⁿsuc x
  sucInt-reflects-< (negsuc (suc x)) (negsuc (suc y)) p = sucⁿ-creates-<ⁿ y x .fst p

  predInt-reflects-< : ∀ x y → [ predInt x < predInt y ] → [ x < y ]
  predInt-reflects-< (pos  zero  ) (pos  zero  ) p = p
  predInt-reflects-< (pos  zero  ) (pos (suc y)) p = 0<ⁿsuc y
  predInt-reflects-< (pos (suc x)) (pos (suc y)) p = sucⁿ-creates-<ⁿ x y .fst p
  predInt-reflects-< (pos  zero  ) (negsuc   y ) p = ¬-<ⁿ-zero p
  predInt-reflects-< (negsuc   x ) (pos      y ) p = tt
  predInt-reflects-< (negsuc   x ) (negsuc   y ) p = sucⁿ-creates-<ⁿ y x .snd p

  sucInt-preserves-< : ∀ x y → [ x < y ] → [ sucInt x < sucInt y ]
  sucInt-preserves-< (pos         x ) (pos         y ) p = sucⁿ-creates-<ⁿ x y .fst p
  sucInt-preserves-< (negsuc  zero  ) (pos         y ) p = 0<ⁿsuc y
  sucInt-preserves-< (negsuc (suc x)) (pos         y ) p = tt
  sucInt-preserves-< (negsuc  zero  ) (negsuc  zero  ) p = p
  sucInt-preserves-< (negsuc  zero  ) (negsuc (suc y)) p = ¬-<ⁿ-zero p
  sucInt-preserves-< (negsuc (suc x)) (negsuc  zero  ) p = tt
  sucInt-preserves-< (negsuc (suc x)) (negsuc (suc y)) p = sucⁿ-creates-<ⁿ y x .snd p

  predInt-preserves-< : ∀ x y → [ x < y ] → [ predInt x < predInt y ]
  predInt-preserves-< (pos  zero  ) (pos  zero  ) p = p
  predInt-preserves-< (pos  zero  ) (pos (suc y)) p = tt
  predInt-preserves-< (pos (suc x)) (pos  zero  ) p = ¬-<ⁿ-zero p
  predInt-preserves-< (pos (suc x)) (pos (suc y)) p = sucⁿ-creates-<ⁿ x y .snd p
  predInt-preserves-< (negsuc   x ) (pos  zero  ) p = 0<ⁿsuc x
  predInt-preserves-< (negsuc   x ) (pos (suc y)) p = tt
  predInt-preserves-< (negsuc   x ) (negsuc   y ) p = sucⁿ-creates-<ⁿ y x .fst p

abstract
  +-preserves-< : ∀ a b x → [ a < b ] → [ (a + x) < (b + x) ]
  +-preserves-< a b (pos zero) a<b = a<b
  +-preserves-< a b (pos (suc n)) a<b = let r = +-preserves-< a b (pos n) a<b
                                        in sucInt-preserves-< (a +pos n) (b +pos n) r
  +-preserves-< a b (negsuc zero) a<b = predInt-preserves-< a b a<b
  +-preserves-< a b (negsuc (suc n)) a<b = let r = +-preserves-< a b (negsuc n) a<b
                                           in predInt-preserves-< (a +negsuc n) (b +negsuc n) r

  +-reflects-< : ∀ a b x → [ (a + x) < (b + x) ] → [ a < b ]
  +-reflects-< a b x = snd (
    (a + x) < (b + x) ⇒ᵖ⟨ +-preserves-< (a + x) (b + x) (- x) ⟩
    ((a + x) + (- x)) < ((b + x) + (- x)) ⇒ᵖ⟨ (pathTo⇐ λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
    (a + (x + (- x))) < (b + (x + (- x))) ⇒ᵖ⟨ (pathTo⇒ λ i → (a + +-inverseʳ x i) < (b + +-inverseʳ x i)) ⟩
    (a + 0) < (b + 0)                     ⇒ᵖ⟨ (λ x → x) ⟩
    a < b             ◼ᵖ)

  +-reflects-<ˡ : ∀ a b x → [ (x + a) < (x + b) ] → [ a < b ]
  +-reflects-<ˡ a b x p = +-reflects-< a b x (transport (λ i → [ +-comm x a i < +-comm x b i ]) p)

abstract
  -- + is <-extentional
  +-<-ext : (w x y z : ℤ) → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
  +-<-ext w x y z r with w ≟ y | x ≟ z
  ... | lt w<y | q = inlᵖ w<y
  ... | eq w≡y | q = inrᵖ (+-reflects-<ˡ x z y (transport (λ i → [ (w≡y i + x) < (y + z) ]) r))
  ... | gt y<w | q = inrᵖ $ case (<-cotrans (w + x) (y + z) r (y + x)) as ((w + x) < (y + x)) ⊔ ((y + x) < (y + z)) ⇒ x < z of λ
    { (inl p) → ⊥-elim {A = λ _ → [ x < z ]} (<-asym y w y<w (+-reflects-< w y x p))
    ; (inr p) → +-reflects-<ˡ x z y p
    }

-- properties about multiplication
abstract
  -- equality of _·_ and _·'_
  ·≡·' : ∀ x y → x · y ≡ x ·' y
  ·≡·' (pos a) (pos b) = refl
  ·≡·' (pos zero) (negsuc b) = refl
  ·≡·' (pos (suc a)) (negsuc b) =
    negsuc   (a ·ⁿ b +ⁿ (a +ⁿ b))  ≡⟨ (λ i → negsuc $ lemma1 a b i) ⟩
    negsuc   (b +ⁿ a ·ⁿ suc b)     ≡⟨ refl ⟩
    neg (suc (b +ⁿ a ·ⁿ suc b))    ∎
  ·≡·' (negsuc a) (pos zero) = λ i → signed sneg $ ·ⁿ-nullifiesʳ a (~ i)
  ·≡·' (negsuc a) (pos (suc b)) = λ i → negsuc $ lemma1 a b i
  ·≡·' (negsuc a) (negsuc b) = refl

  ·'-nullifiesʳ : ∀ x → x ·' 0 ≡ 0
  ·'-nullifiesʳ (pos    n) i = signed spos (·ⁿ-nullifiesʳ n i)
  ·'-nullifiesʳ (negsuc n) i = signed sneg (·ⁿ-nullifiesʳ n i)

  ·'-nullifiesˡ : ∀ x → 0 ·' x ≡ 0
  ·'-nullifiesˡ (pos    n) i = pos (·ⁿ-nullifiesˡ n i)
  ·'-nullifiesˡ (negsuc n)   = refl

abstract
  -distrˡ : ∀ a b → -(a · b) ≡ (- a) · b
  -distrˡ (pos   zero ) (pos  zero  ) = refl
  -distrˡ (pos   zero ) (pos (suc b)) = refl
  -distrˡ (pos (suc a)) (pos  zero  ) = λ i → - pos (·ⁿ-nullifiesʳ a i)
  -distrˡ (pos (suc a)) (pos (suc b)) = λ i → negsuc $ lemma1 a b (~ i)
  -distrˡ (pos  zero  ) (negsuc   b ) = refl
  -distrˡ (pos (suc a)) (negsuc   b ) = λ i → pos $ suc $ lemma1 a b i
  -distrˡ (negsuc   a ) (pos  zero  ) = λ i → pos (·ⁿ-nullifiesʳ a (~ i))
  -distrˡ (negsuc   a ) (pos (suc b)) = λ i → pos $ suc $ lemma1 a b i
  -distrˡ (negsuc   a ) (negsuc   b ) = λ i → negsuc $ lemma1 a b (~ i)

abstract
  ·-comm : ∀ a b → a · b ≡ b · a
  ·-comm (pos      a ) (pos      b ) = λ i → pos $ ·ⁿ-comm a b i
  ·-comm (pos  zero  ) (negsuc   b ) = refl
  ·-comm (pos (suc a)) (negsuc   b ) = λ i → negsuc $ ·ⁿ-comm a b i +ⁿ +ⁿ-comm a b i
  ·-comm (negsuc   a ) (pos  zero  ) = refl
  ·-comm (negsuc   a ) (pos (suc b)) = λ i → negsuc $ ·ⁿ-comm a b i +ⁿ +ⁿ-comm a b i
  ·-comm (negsuc   a ) (negsuc   b ) i = pos (suc (lemma7 a b i))

  -distrʳ : ∀ a b → -(a · b) ≡ a · (- b)
  -distrʳ a b = (λ i → - ·-comm a b i) ∙ -distrˡ b a ∙ ·-comm (- b) a

abstract
  -- this proof of associativity is ported from `Data.Integer.Properties` which works on
  --   _·_ : ℤ → ℤ → ℤ
  --   i · j = sign i S· sign j ◃ ∣ i ∣ ℕ· ∣ j ∣

  ·'-assoc : ∀ x y z → (x ·' y) ·' z ≡ x ·' (y ·' z)
  ·'-assoc (pos 0) y z = (λ i → ·'-nullifiesˡ y i ·' z) ∙ ·'-nullifiesˡ z ∙ sym (·'-nullifiesˡ (y ·' z))
  ·'-assoc x (pos 0) z = (λ i → ·'-nullifiesʳ x i ·' z) ∙ ·'-nullifiesˡ z ∙ sym (·'-nullifiesʳ x)  ∙ (λ i → x ·' ·'-nullifiesˡ z (~ i))
  ·'-assoc x y (pos 0) = ·'-nullifiesʳ (x ·' y) ∙ sym (·'-nullifiesʳ x) ∙ (λ i → x ·' ·'-nullifiesʳ y (~ i))
  ·'-assoc (negsuc   a ) (negsuc   b ) (pos (suc c)) = λ i → (pos (suc (lemma2 a b c i)))
  ·'-assoc (negsuc   a ) (pos (suc b)) (negsuc   c ) = λ i → (pos (suc (lemma2 a b c i)))
  ·'-assoc (pos (suc a)) (pos (suc b)) (pos (suc c)) = λ i → (pos (suc (lemma2 a b c i)))
  ·'-assoc (pos (suc a)) (negsuc   b ) (negsuc   c ) = λ i → (pos (suc (lemma2 a b c i)))
  ·'-assoc (negsuc   a ) (negsuc   b ) (negsuc   c ) = λ i → (negsuc   (lemma2 a b c i) )
  ·'-assoc (negsuc   a ) (pos (suc b)) (pos (suc c)) = λ i → (negsuc   (lemma2 a b c i) )
  ·'-assoc (pos (suc a)) (negsuc   b ) (pos (suc c)) = λ i → (negsuc   (lemma2 a b c i) )
  ·'-assoc (pos (suc a)) (pos (suc b)) (negsuc   c ) = λ i → (negsuc   (lemma2 a b c i) )

abstract
  -- equality of associativity on _·_ and _·'_
  ·'-assoc≡ : ∀ x y z
            → ((x ·  y) ·  z ≡ x ·  (y ·  z))
            ≡ ((x ·' y) ·' z ≡ x ·' (y ·' z))
  ·'-assoc≡ x y z i = ·≡·' (·≡·' x y i) z i ≡ ·≡·' x (·≡·' y z i) i

  -- associativity of _·_ from associativiy of _·'_
  ·-assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
  ·-assoc x y z = transport (sym (·'-assoc≡ x y z)) (·'-assoc x y z)

abstract
  ·-nullifiesˡ : ∀ x → 0 · x ≡ 0
  ·-nullifiesˡ (pos n) = refl
  ·-nullifiesˡ (negsuc n) = refl

  ·-nullifiesʳ : ∀ x → x · 0 ≡ 0
  ·-nullifiesʳ x = ·-comm x 0 ∙ ·-nullifiesˡ x

  ·-identityˡ : ∀ x → 1 · x ≡ x
  ·-identityˡ (pos n) = λ i → pos $ +ⁿ-comm n 0 i
  ·-identityˡ (negsuc n) = refl

  ·-identityʳ : ∀ x → x · 1 ≡ x
  ·-identityʳ x = ·-comm x 1 ∙ ·-identityˡ x

abstract
  ·-preserves-< : (x y z : ℤ) → [ 0 < z ] → [ x < y ] → [ (x · z) < (y · z) ]
  ·-preserves-< (pos    x) (pos    y) (pos      z ) p q = ·ⁿ-preserves-<ⁿ x y z p q
  ·-preserves-< (negsuc x) (pos    y) (pos  zero  ) p q = subst (λ p → [ 0 <ⁿ p ]) (sym $ ·ⁿ-nullifiesʳ y) p
  ·-preserves-< (negsuc x) (pos    y) (pos (suc z)) p q = tt
  ·-preserves-< (negsuc x) (negsuc y) (pos  zero  ) p q = p
  ·-preserves-< (negsuc x) (negsuc y) (pos (suc z)) p q = (
       y                   <ⁿ  x                   ⇒ᵖ⟨ ·ⁿ-preserves-<ⁿ y x (suc z) (0<ⁿsuc z) ⟩
      (y ·ⁿ suc z        ) <ⁿ (x ·ⁿ suc z        ) ⇒ᵖ⟨ +ⁿ-createsʳ-<ⁿ (y ·ⁿ suc z) (x ·ⁿ suc z) z .fst ⟩
      (y ·ⁿ suc z +ⁿ z   ) <ⁿ (x ·ⁿ suc z +ⁿ z   ) ⇒ᵖ⟨ pathTo⇐ (λ i → lemma3 y z i <ⁿ lemma3 x z i) ⟩
      (y ·ⁿ z +ⁿ (y +ⁿ z)) <ⁿ (x ·ⁿ z +ⁿ (x +ⁿ z)) ◼ᵖ) .snd q

  ·-reflects-< : (x y z : ℤ) → [ 0 < z ] → [ (x · z) < (y · z) ] → [ x < y ]
  ·-reflects-< (pos    x) (pos    y) (pos      z ) p q = ·ⁿ-reflects-<ⁿ x y z p q
  ·-reflects-< (pos    x) (negsuc y) (pos  zero  ) p q = <ⁿ-irrefl 0 p
  ·-reflects-< (negsuc x) (pos    y) (pos  zero  ) p q = tt
  ·-reflects-< (negsuc x) (pos    y) (pos (suc z)) p q = tt
  ·-reflects-< (negsuc x) (negsuc y) (pos  zero  ) p (k , q) = ⊥-elim {A = λ _ → [ y <ⁿ x ]} $ snotzⁿ (sym (+ⁿ-suc k 0) ∙ q)
  ·-reflects-< (negsuc x) (negsuc y) (pos (suc z)) p q = (
    (y ·ⁿ z +ⁿ (y +ⁿ z)) <ⁿ (x ·ⁿ z +ⁿ (x +ⁿ z)) ⇒ᵖ⟨ pathTo⇒ (λ i → +ⁿ-assoc (y ·ⁿ z) y z i <ⁿ +ⁿ-assoc (x ·ⁿ z) x z i) ⟩
    ((y ·ⁿ z +ⁿ y) +ⁿ z) <ⁿ ((x ·ⁿ z +ⁿ x) +ⁿ z) ⇒ᵖ⟨ +ⁿ-createsʳ-<ⁿ (y ·ⁿ z +ⁿ y) (x ·ⁿ z +ⁿ x) z .snd ⟩
    (y ·ⁿ z +ⁿ y       ) <ⁿ (x ·ⁿ z +ⁿ x       ) ⇒ᵖ⟨ pathTo⇒ (λ i → γ y i <ⁿ γ x i) ⟩
    (y ·ⁿ suc z        ) <ⁿ (x ·ⁿ suc z        ) ⇒ᵖ⟨ ·ⁿ-reflects-<ⁿ y x (suc z) (0<ⁿsuc z) ⟩
     y                   <ⁿ  x                   ◼ᵖ) .snd q where
     γ : ∀ x → x ·ⁿ z +ⁿ x ≡ x ·ⁿ suc z
     γ x = sym $ ·ⁿ-comm x (suc z) ∙ +ⁿ-comm x (z ·ⁿ x) ∙ (λ i → ·ⁿ-comm z x i +ⁿ x)

abstract
  ·-sucInt : ∀ m n → (m · sucInt n) ≡ (m + (m · n))
  ·-sucInt (pos      a ) (pos      b ) = (λ i → pos (·ⁿ-suc a b i)) ∙ sym (pos+pos≡+ⁿ a (a ·ⁿ b))
  ·-sucInt (pos  zero  ) (negsuc   b ) = ·-nullifiesˡ _
  ·-sucInt (pos (suc a)) (negsuc zero) =
    pos (a ·ⁿ zero)                                  ≡⟨ (λ i → pos $ ·ⁿ-nullifiesʳ a i) ⟩
    pos 0                                            ≡⟨ sym $ +-inverse (pos (suc a)) .fst ⟩
    (pos (suc a) +negsuc                a          ) ≡⟨ refl ⟩
    (pos (suc a) +negsuc (     zero +ⁿ  a         )) ≡⟨ (λ i → pos (suc a) +negsuc (sym (·ⁿ-nullifiesʳ a) i +ⁿ +ⁿ-comm 0 a i)) ⟩
    (pos (suc a) +negsuc (a ·ⁿ zero +ⁿ (a +ⁿ zero))) ∎
  ·-sucInt (pos (suc a)) (negsuc (suc b)) =
    negsuc (a ·ⁿ b +ⁿ (a +ⁿ b))                          ≡⟨ sym $ +negsuc-identityˡ (a ·ⁿ b +ⁿ (a +ⁿ b)) ⟩
    0 +negsuc (a ·ⁿ b +ⁿ (a +ⁿ b))                       ≡⟨ (λ i → possuc+negsuc≡0 a (~ i) +negsuc (a ·ⁿ b +ⁿ (a +ⁿ b))) ⟩
    (pos (suc a) +negsuc a) +negsuc (a ·ⁿ b +ⁿ (a +ⁿ b)) ≡⟨ sym $ +negsuc-assoc (pos (suc a)) a (a ·ⁿ b +ⁿ (a +ⁿ b)) ⟩
    pos (suc a) +negsuc (a +ⁿ suc (a ·ⁿ b +ⁿ (a +ⁿ b)))  ≡⟨ (λ i → pos (suc a) +negsuc (lemma4 a b (~ i))) ⟩
    pos (suc a) +negsuc (a ·ⁿ suc b +ⁿ (a +ⁿ suc b))     ∎
  ·-sucInt (negsuc   a ) (pos  zero  ) = λ i → negsuc $ ·ⁿ-nullifiesʳ a i +ⁿ +ⁿ-comm a 0 i
  ·-sucInt (negsuc   a ) (pos (suc b)) =
    negsuc (a ·ⁿ suc b +ⁿ (a +ⁿ suc b))    ≡⟨ (λ i → negsuc $ lemma4 a b i) ⟩
    negsuc (a +ⁿ suc (a ·ⁿ b +ⁿ (a +ⁿ b))) ≡⟨ (λ i → negsuc $ +ⁿ-suc a (a ·ⁿ b +ⁿ (a +ⁿ b)) i) ∙ sym (negsuc+negsuc≡+ⁿ a (a ·ⁿ b +ⁿ (a +ⁿ b))) ⟩
    negsuc a +negsuc (a ·ⁿ b +ⁿ (a +ⁿ b))  ∎
  ·-sucInt (negsuc a) (negsuc zero) = sym (+-inverse (pos (suc a)) .snd) ∙ (λ i → sucInt (negsuc a +pos (·ⁿ-identityʳ a (~ i))))
  ·-sucInt (negsuc a) (negsuc (suc b)) =
    pos (suc (b +ⁿ a ·ⁿ suc b))                                ≡⟨ refl ⟩
    sucInt (pos (b +ⁿ a ·ⁿ suc b))                             ≡⟨ (λ i → sucInt $ sucInt[negsuc+pos]≡pos (b +ⁿ a ·ⁿ suc b) (~ i)) ⟩
    sucInt (sucInt (negsuc 0 +pos (b +ⁿ a ·ⁿ suc b)))          ≡⟨ (λ i → sucInt (sucInt (+pos-inverse a (~ i) +pos (b +ⁿ a ·ⁿ suc b)))) ⟩
    sucInt (sucInt ((negsuc a +pos a) +pos (b +ⁿ a ·ⁿ suc b))) ≡⟨ (λ i → sucInt $ sucInt $ +pos-assoc (negsuc a) a (b +ⁿ a ·ⁿ suc b) i) ⟩
    sucInt (sucInt (negsuc a +pos (a +ⁿ (b +ⁿ a ·ⁿ suc b))))   ≡⟨ (λ i → sucInt (sucInt (negsuc a +pos lemma5 a b i))) ⟩
    sucInt (sucInt (negsuc a +pos (b +ⁿ a ·ⁿ suc (suc b))))    ∎

abstract
  ·-sucIntˡ : ∀ m n → (sucInt m · n) ≡ (n + (m · n))
  ·-sucIntˡ m n = ·-comm (sucInt m) n ∙ ·-sucInt n m ∙ λ i → n + ·-comm n m i

  ·-predInt : ∀ m n → (m · predInt n) ≡ ((- m) + (m · n))
  ·-predInt m (pos zero) = ·-comm m (negsuc 0) ∙ -1·≡- m ∙ λ i → (- m) + ·-nullifiesʳ m (~ i)
  ·-predInt m (pos (suc n)) =
    m · pos n                 ≡⟨ +-comm (m · pos n) 0 ⟩
    0 + m · pos n             ≡⟨ (λ i → +-inverseˡ m (~ i) + (m · pos n)) ⟩
    ((- m) + m) + (m · pos n) ≡⟨ sym $ +-assoc (- m) m (m · pos n) ⟩
    (- m) + (m + (m · pos n)) ≡⟨ (λ i → (- m) + ·-sucInt m (pos n) (~ i)) ⟩
    (- m) + (m · pos (suc n)) ∎
  ·-predInt (pos zero) (negsuc zero) = refl
  ·-predInt (pos (suc n)) (negsuc zero) = (λ i → negsuc $ ·ⁿ-identityʳ n i +ⁿ +ⁿ-comm n 1 i) ∙ (λ i → negsuc $ +ⁿ-comm n (suc n) i) ∙ sym (negsuc+negsuc≡+ⁿ n n) ∙ (λ i → negsuc n +negsuc (·ⁿ-nullifiesʳ n (~ i) +ⁿ +ⁿ-comm 0 n i))
  ·-predInt (pos zero) (negsuc (suc m)) = refl
  ·-predInt (pos (suc n)) (negsuc (suc m)) =
    negsuc (n ·ⁿ suc (suc m) +ⁿ (n +ⁿ suc (suc m)))  ≡⟨ (λ i → negsuc $ ·ⁿ-suc n (suc m) i +ⁿ +ⁿ-suc n (suc m) i) ⟩
    negsuc ((n +ⁿ n ·ⁿ suc m) +ⁿ suc (n +ⁿ suc m))   ≡⟨ (λ i → negsuc $ +ⁿ-assoc n (n ·ⁿ suc m) (suc n +ⁿ suc m) (~ i)) ⟩
    negsuc (n +ⁿ (n ·ⁿ suc m +ⁿ suc (n +ⁿ suc m)))   ≡⟨ (λ i → negsuc $ n +ⁿ +ⁿ-suc (n ·ⁿ suc m) (n +ⁿ suc m) i) ⟩
    negsuc (n +ⁿ suc (n ·ⁿ suc m +ⁿ (n +ⁿ suc m)))   ≡⟨ (λ i → negsuc $ +ⁿ-suc n (n ·ⁿ suc m +ⁿ (n +ⁿ suc m)) i) ⟩
    negsuc (suc (n +ⁿ (n ·ⁿ suc m +ⁿ (n +ⁿ suc m)))) ≡⟨ sym $ negsuc+negsuc≡+ⁿ n (n ·ⁿ suc m +ⁿ (n +ⁿ suc m)) ⟩
    (negsuc n +negsuc (n ·ⁿ suc m +ⁿ (n +ⁿ suc m)))  ∎
  ·-predInt (negsuc n) (negsuc zero) = cong sucInt ((λ i → pos $ suc $ ·ⁿ-suc n 1 i) ∙ sym (pos+pos≡+ⁿ (suc n) (n ·ⁿ 1)))
  ·-predInt (negsuc n) (negsuc (suc m)) =
    pos (suc (suc (suc (m +ⁿ n ·ⁿ suc (suc (suc m))))))        ≡⟨ refl ⟩
    sucInt (sucInt (pos (suc (m +ⁿ n ·ⁿ suc (suc (suc m))))))  ≡⟨ (λ i → sucInt $ sucInt $ pos $ lemma6 m n i) ⟩
    sucInt (sucInt (pos (suc n +ⁿ (m +ⁿ n ·ⁿ suc (suc m)))))   ≡⟨ (λ i → sucInt $ sucInt $ pos+pos≡+ⁿ (suc n) (m +ⁿ n ·ⁿ suc (suc m)) (~ i)) ⟩
    sucInt (sucInt (pos (suc n) +pos (m +ⁿ n ·ⁿ suc (suc m)))) ∎

abstract
  ·-predIntˡ : ∀ m n → (predInt m · n) ≡ ((- n) + (m · n))
  ·-predIntˡ m n = ·-comm (predInt m) n ∙ ·-predInt n m ∙ λ i → (- n) + (·-comm n m i)

  -distrib : ∀ m n → -(m + n) ≡ (- m) + (- n)
  -distrib (pos zero) (pos zero) = refl
  -distrib (pos (suc n)) (pos zero) = refl
  -distrib (pos zero) (pos (suc m)) =
    - sucInt (pos zero +pos m) ≡⟨ (λ i → - sucInt (pos+pos≡+ⁿ 0 m i)) ⟩
    negsuc m                   ≡⟨ sym $ +negsuc-identityˡ m ⟩
    (pos zero +negsuc m)       ∎
  -distrib (pos (suc n)) (pos (suc m)) = (λ i → - sucInt (pos+pos≡+ⁿ (suc n) m i)) ∙ sym (negsuc+negsuc≡+ⁿ n m)
  -distrib (pos zero) (negsuc m) = (λ i → - +negsuc-identityˡ m i) ∙ sym (pos+pos≡+ⁿ 0 (suc m))
  -distrib (pos (suc n)) (negsuc m) = sym (pos+negsuc-swap m n) ∙ pos+negsuc≡negsuc+pos (suc m) n
  -distrib (negsuc n) (pos zero) = refl
  -distrib (negsuc n) (pos (suc m)) = (λ i → - pos+negsuc≡negsuc+pos (suc m) n (~ i)) ∙ sym (pos+negsuc-swap n m)
  -distrib (negsuc n) (negsuc m) = (λ i → - negsuc+negsuc≡+ⁿ n m i) ∙ (λ i → sucInt $ pos+pos≡+ⁿ (suc n) m (~ i))

abstract
  ·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
  ·-distribˡ (pos zero) m n = (λ i → ·-nullifiesˡ m i + ·-nullifiesˡ n i) ∙ (sym $ ·-nullifiesˡ (m + n))
  ·-distribˡ (pos (suc o)) m n = let
    ind = ·-distribˡ (pos o) m n
    lhs = (pos (suc o) · m) + (pos (suc o) · n)  ≡⟨ (λ i → ·-sucIntˡ (pos o) m i + ·-sucIntˡ (pos o) n i) ⟩
          (m + (pos o · m)) + (n + (pos o · n))  ≡⟨ sym $ +-assoc m (pos o · m) (n + (pos o · n)) ⟩
           m + ((pos o · m) + (n + (pos o · n))) ≡⟨ (λ i → m + +-comm (pos o · m) (n + (pos o · n)) i) ⟩
           m + ((n + (pos o · n)) + (pos o · m)) ≡⟨ (λ i → m + +-assoc n (pos o · n) (pos o · m) (~ i)) ⟩
           m + (n + ((pos o · n) + (pos o · m))) ≡⟨ (λ i → +-assoc m n (+-comm (pos o · n) (pos o · m) i) i) ⟩
          (m + n) + ((pos o · m) + (pos o · n))  ≡⟨ (λ i → (m + n) + ind i) ⟩
          (m + n) + (pos o · (m + n))            ∎
    rhs = (pos (suc o) · (m + n))       ≡⟨ refl ⟩
          (sucInt (pos o) · (m + n))    ≡⟨ ·-sucIntˡ (pos o) (m + n) ⟩
          ((m + n) + (pos o · (m + n))) ∎
    in lhs ∙ sym rhs
  ·-distribˡ (negsuc zero) (pos zero) (pos zero) = refl
  ·-distribˡ (negsuc zero) (pos zero) (pos (suc n)) = +negsuc-identityˡ n ∙ λ i → negsuc 0 · sucInt (pos+pos≡+ⁿ 0 n (~ i))
  ·-distribˡ (negsuc zero) (pos (suc m)) (pos zero) = refl
  ·-distribˡ (negsuc zero) (pos (suc m)) (pos (suc n)) = negsuc+negsuc≡+ⁿ m n ∙ λ i → negsuc 0 · sucInt (pos+pos≡+ⁿ (suc m) n (~ i))
  ·-distribˡ (negsuc zero) (pos zero) (negsuc n) = (λ i → sucInt $ pos+pos≡+ⁿ 0 (n +ⁿ 0) i) ∙ (λ i → negsuc 0 · +negsuc-identityˡ n (~ i))
  ·-distribˡ (negsuc zero) (pos (suc m)) (negsuc n) =
    sucInt (negsuc m +pos (n +ⁿ zero))           ≡⟨ (λ i → sucInt $ negsuc m +pos +ⁿ-comm n 0 i) ⟩
    sucInt (negsuc m +pos n)                     ≡⟨ refl ⟩
    negsuc m +pos (suc n)                        ≡⟨ negsuc+pos-swap m n ⟩
    - (negsuc n +pos (suc m))                    ≡⟨ (λ i → - pos+negsuc≡negsuc+pos (suc m) n (~ i)) ⟩
    - (pos (suc m) +negsuc n)                    ≡⟨ sym $ -1·≡- (pos (suc m) +negsuc n) ⟩
    negsuc zero · (pos (suc m) +negsuc n)        ∎
  ·-distribˡ (negsuc zero) (negsuc m) (pos zero) = refl
  ·-distribˡ (negsuc zero) (negsuc m) (pos (suc n)) =
    pos (suc (m +ⁿ zero)) +negsuc n        ≡⟨ (λ i → pos (suc (+ⁿ-comm m 0 i)) +negsuc n) ⟩
    pos (suc m) +negsuc n                  ≡⟨ pos+negsuc≡negsuc+pos (suc m) n ⟩
    sucInt (negsuc n +pos m)               ≡⟨ negsuc+pos-swap n m ⟩
    - negsuc m +pos (suc n)                ≡⟨ refl ⟩
    - sucInt (negsuc m +pos n)             ≡⟨ sym $ -1·≡- (sucInt (negsuc m +pos n)) ⟩
    negsuc zero · sucInt (negsuc m +pos n) ∎
  ·-distribˡ (negsuc zero) (negsuc m) (negsuc n) =
    sucInt (pos (suc (m +ⁿ zero)) +pos (n +ⁿ zero)) ≡⟨ (λ i → sucInt (pos (suc (+ⁿ-comm m 0 i)) +pos (+ⁿ-comm n 0 i))) ⟩
    sucInt (pos (suc m) +pos (n))                   ≡⟨ (λ i → sucInt $ pos+pos≡+ⁿ (suc m) n i) ⟩
    sucInt (pos (suc m +ⁿ n))                       ≡⟨ refl ⟩
    pos (suc (suc (m +ⁿ n)))                        ≡⟨ (λ i → pos $ suc $ suc $ +ⁿ-comm 0 (m +ⁿ n) i) ⟩
    negsuc zero · (negsuc (suc (m +ⁿ n)))           ≡⟨ (λ i → negsuc zero · negsuc+negsuc≡+ⁿ m n (~ i)) ⟩
    negsuc zero · (negsuc m +negsuc n)              ∎
  ·-distribˡ (negsuc (suc o)) m n = let
    r = ·-distribˡ (negsuc o) m n
    lhs = (negsuc (suc o) · m) + (negsuc (suc o) · n)          ≡⟨ (λ i → ·-predIntˡ (negsuc o) m i + ·-predIntˡ (negsuc o) n i) ⟩
          ((- m) + (negsuc o · m)) + ((- n) + (negsuc o · n))  ≡⟨ sym $ +-assoc (- m)  (negsuc o · m) ((- n) + (negsuc o · n)) ⟩
           (- m) + ((negsuc o · m) + ((- n) + (negsuc o · n))) ≡⟨ (λ i → (- m) + +-comm (negsuc o · m) ((- n) + (negsuc o · n)) i) ⟩
           (- m) + (((- n) + (negsuc o · n)) + (negsuc o · m)) ≡⟨ (λ i → (- m) + +-assoc (- n) (negsuc o · n) (negsuc o · m) (~ i)) ⟩
           (- m) + ((- n) + ((negsuc o · n) + (negsuc o · m))) ≡⟨ (λ i → +-assoc (- m) (- n) (+-comm (negsuc o · n) (negsuc o · m) i) i) ⟩
          ((- m) + (- n)) + ((negsuc o · m) + (negsuc o · n))  ≡⟨ (λ i → ((- m) + (- n)) + r i) ⟩
          ((- m) + (- n)) + (negsuc o · (m + n))            ∎
    rhs = negsuc (suc o) · (m + n)               ≡⟨ ·-predIntˡ (negsuc o) (m + n) ⟩
          (- (m + n)) + negsuc (o) · (m + n)     ≡⟨ (λ i → -distrib m n i + negsuc (o) · (m + n)) ⟩
          ((- m) + (- n)) + (negsuc (o) · (m + n)) ∎
    in lhs ∙ sym rhs

abstract
  ·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
  ·-distribʳ m n o = transport (sym λ i → ·-comm m o i + ·-comm n o i ≡ ·-comm (m + n) o i) $ ·-distribˡ o m n

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℤ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _·_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℤ
·-Semigroup .IsSemigroup.is-assoc x y z = sym (·-assoc x y z)

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-identityʳ x , +-identityˡ x

·-Monoid : [ isMonoid 1 _·_ ]
·-Monoid .IsMonoid.is-Semigroup = ·-Semigroup
·-Monoid .IsMonoid.is-identity x = ·-identityʳ x , ·-identityˡ x

is-Semiring : [ isSemiring 0 1 _+_ _·_ ]
is-Semiring .IsSemiring.+-Monoid = +-Monoid
is-Semiring .IsSemiring.·-Monoid = ·-Monoid
is-Semiring .IsSemiring.+-comm   = +-comm
is-Semiring .IsSemiring.is-dist x y z = sym (·-distribˡ x y z) , sym (·-distribʳ x y z)

is-CommSemiring : [ isCommSemiring 0 1 _+_ _·_ ]
is-CommSemiring .IsCommSemiring.is-Semiring = is-Semiring
is-CommSemiring .IsCommSemiring.·-comm      = ·-comm

<-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = <-irrefl
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  a b c = <-trans a b c
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho a b with a ≟ b
... | lt a<b = inl (inl a<b)
... | eq a≡b = inr ∣ a≡b ∣
... | gt b<a = inl (inr b<a)

≤-Lattice : [ isLattice (λ x y → ¬ᵖ (y < x)) min max ]
≤-Lattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-Lattice .IsLattice.is-min         = is-min
≤-Lattice .IsLattice.is-max         = is-max

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _·_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-Lattice           = ≤-Lattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = +-<-ext
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = ·-preserves-<

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _·_ -_ _<_ min max ]
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.+-inverse                      = +-inverse

ℤbundle : LinearlyOrderedCommRing {ℓ-zero} {ℓ-zero}
ℤbundle .LinearlyOrderedCommRing.Carrier                    = ℤ
ℤbundle .LinearlyOrderedCommRing.0f                         = 0
ℤbundle .LinearlyOrderedCommRing.1f                         = 1
ℤbundle .LinearlyOrderedCommRing._+_                        = _+_
ℤbundle .LinearlyOrderedCommRing._·_                        = _·_
ℤbundle .LinearlyOrderedCommRing.-_                         = -_
ℤbundle .LinearlyOrderedCommRing.min                        = min
ℤbundle .LinearlyOrderedCommRing.max                        = max
ℤbundle .LinearlyOrderedCommRing._<_                        = _<_
ℤbundle .LinearlyOrderedCommRing.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing

-- ·-reflects-≡ˡ : ∀ a b x → (pos (suc x)) ·' a ≡ (pos (suc x)) ·' b → a ≡ b
-- ·-reflects-≡ˡ a b x p = {!   !}

-- private
--   ¬0≡suc
--   ¬0≡possuc
--   ¬0≡negsuc
--   ¬pos≡negsuc
--
-- ·-reflects-≡ʳ : ∀ a b x → a · (pos (suc x)) ≡ b · (pos (suc x)) → a ≡ b
-- ·-reflects-≡ʳ (pos      0 ) (pos      0 ) x q = refl
-- ·-reflects-≡ʳ (pos      0 ) (pos (suc b)) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (pos (suc a)) (pos      0 ) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (pos (suc a)) (pos (suc b)) x q i = sucInt $ ·-reflects-≡ʳ (pos a) (pos b) x {!   !} i
-- ·-reflects-≡ʳ (pos      0 ) (negsuc   b ) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (pos (suc a)) (negsuc   b ) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (negsuc   a ) (pos      0 ) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (negsuc   a ) (pos (suc b)) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (negsuc zero) (negsuc zero) x q = refl
-- ·-reflects-≡ʳ (negsuc zero) (negsuc (suc b)) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (negsuc (suc a)) (negsuc zero) x q = {! ⊥  !}
-- ·-reflects-≡ʳ (negsuc (suc a)) (negsuc (suc b)) x q i = predInt $ ·-reflects-≡ʳ (negsuc a) (negsuc b) x {!   !} i
