{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Instances.QuoIntFromInt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything hiding (⋆) renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
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
open import Cubical.Foundations.Univalence

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

import Agda.Builtin.Int as Builtin
import Data.Integer.Base as BuiltinBase
import Data.Integer.Properties as BuiltinProps

open import Cubical.Data.Nat.Literals
open import SyntheticReals.Number.Prelude.Nat
open import SyntheticReals.Number.Prelude.Int
import Cubical.Data.Int as Int
import SyntheticReals.Number.Instances.Int

open import Cubical.HITs.Ints.QuoInt as QuoInt using
  ( ℤ
  ; _+_
  ; -_
  ; Int≡ℤ
  ; signed
  ; posneg
  ; ℤ→Int
  ; sucℤ
  ; predℤ
  ; sign
  ; abs
  ; pos
  ; neg
  ; +-comm
  ; +-assoc
  ; sucℤ-+ʳ
  ) renaming
  ( _*_ to _·_ )

ℤ≡Int = sym Int≡ℤ

private
  _·ᵗʳ_ : Int → Int → Int
  _·ᵗʳ_ = transport (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _·_

  ·≡·ᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _·_ _·ᵗʳ_
  ·≡·ᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j)) (~ i) _·_

  lemma1 : ∀ a b → b +ⁿ a ·ⁿ suc b ≡ a ·ⁿ b +ⁿ (a +ⁿ b)
  lemma1 a b =
    b +ⁿ a ·ⁿ suc b    ≡⟨ (λ i → b +ⁿ ·ⁿ-suc a b i) ⟩
    b +ⁿ (a +ⁿ a ·ⁿ b) ≡⟨ +ⁿ-assoc b a (a ·ⁿ b) ⟩
    (b +ⁿ a) +ⁿ a ·ⁿ b ≡⟨ (λ i → +ⁿ-comm b a i +ⁿ a ·ⁿ b) ⟩
    (a +ⁿ b) +ⁿ a ·ⁿ b ≡⟨ +ⁿ-comm (a +ⁿ b) (a ·ⁿ b) ⟩
    a ·ⁿ b +ⁿ (a +ⁿ b) ∎

  ·ᵗʳ≡'·ᶻ : ∀ a b → a ·ᵗʳ b ≡ a ·ᶻ b
  ·ᵗʳ≡'·ᶻ (posᶻ      0 ) (posᶻ      0 )   = refl
  ·ᵗʳ≡'·ᶻ (posᶻ      0 ) (posᶻ (suc b))   = refl
  ·ᵗʳ≡'·ᶻ (posᶻ (suc a)) (posᶻ      0 )   = refl
  ·ᵗʳ≡'·ᶻ (posᶻ (suc a)) (posᶻ (suc b))   = refl
  ·ᵗʳ≡'·ᶻ (posᶻ      0 ) (negsucᶻ   b )   = refl
  ·ᵗʳ≡'·ᶻ (posᶻ (suc a)) (negsucᶻ   b ) i = negsucᶻ (lemma1 a b i)
  ·ᵗʳ≡'·ᶻ (negsucᶻ   a ) (posᶻ      0 ) i = ℤ→Int (signed sneg (·ⁿ-nullifiesʳ a i))
  ·ᵗʳ≡'·ᶻ (negsucᶻ   a ) (posᶻ (suc b)) i = negsucᶻ (lemma1 a b i)
  ·ᵗʳ≡'·ᶻ (negsucᶻ   a ) (negsucᶻ   b )   = refl

  ·ᵗʳ≡·ᶻ : _·ᵗʳ_ ≡ _·ᶻ_
  ·ᵗʳ≡·ᶻ i a b = ·ᵗʳ≡'·ᶻ a b i

·≡·ᶻ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _·_ _·ᶻ_
·≡·ᶻ = J (λ _⋆_ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _·_ _⋆_) ·≡·ᵗʳ ·ᵗʳ≡·ᶻ

-- ·-assoc''''' : ∀ a b c → a · (b · c) ≡ (a · b) · c
-- ·-assoc''''' = transport γ ·-assoc where
--   γ : ((m n o : Z) → m · (n · o) ≡ (m · n) · o)
--     ≡ ((a b c : ℤ) → a · (b · c) ≡ (a · b) · c)
--   γ i = let _⋆_ = QuoInt·≡· i in (x y z : ℤ≡Int i) → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z

sucInt-preserves-ℤ→Int : ∀ a → sucInt (ℤ→Int a) ≡ ℤ→Int (sucℤ a)
sucInt-preserves-ℤ→Int (signed spos n) = refl
sucInt-preserves-ℤ→Int (signed sneg zero) = refl
sucInt-preserves-ℤ→Int (signed sneg (suc zero)) = refl
sucInt-preserves-ℤ→Int (signed sneg (suc (suc n))) = refl
sucInt-preserves-ℤ→Int (posneg i) = refl

predInt-preserves-ℤ→Int : ∀ a → predInt (ℤ→Int a) ≡ ℤ→Int (predℤ a)
predInt-preserves-ℤ→Int (signed spos zero) = refl
predInt-preserves-ℤ→Int (signed spos (suc n)) = refl
predInt-preserves-ℤ→Int (signed sneg zero) = refl
predInt-preserves-ℤ→Int (signed sneg (suc n)) = refl
predInt-preserves-ℤ→Int (posneg i) = refl

-sucℤ-sucℤ≡id : ∀ a → - sucℤ (- sucℤ a) ≡ a
-sucℤ-sucℤ≡id (signed spos n) = refl
-sucℤ-sucℤ≡id (signed sneg zero) = posneg
-sucℤ-sucℤ≡id (signed sneg (suc n)) = refl
-sucℤ-sucℤ≡id (posneg i) j = posneg (i ∧ j)

sucℤ-sucℤ-≡id : ∀ a → sucℤ (- sucℤ (- a)) ≡ a
sucℤ-sucℤ-≡id (signed spos zero) i = posneg (~ i)
sucℤ-sucℤ-≡id (signed spos (suc n)) = refl
sucℤ-sucℤ-≡id (signed sneg n) = refl
sucℤ-sucℤ-≡id (posneg i) j = posneg (i ∨ (~ j))

-sucℤ-sucℤ≡sucℤ-sucℤ- : ∀ a → - sucℤ (- sucℤ a) ≡ sucℤ (- sucℤ (- a))
-sucℤ-sucℤ≡sucℤ-sucℤ- a = -sucℤ-sucℤ≡id a ∙ sym (sucℤ-sucℤ-≡id a)

private
  _+ᵗʳ_ : Int → Int → Int
  _+ᵗʳ_ = transport (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _+_

  +≡+ᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _+_ _+ᵗʳ_
  +≡+ᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j)) (~ i) _+_

  +ᵗʳ≡'+ᶻ : ∀ a b → a +ᵗʳ b ≡ a +ᶻ b
  +ᵗʳ≡'+ᶻ (posᶻ      0 ) (posᶻ      0 )   = refl
  +ᵗʳ≡'+ᶻ (posᶻ      0 ) (posᶻ (suc b))  i = sucInt (Int.+-comm (posᶻ b) 0 i)
  +ᵗʳ≡'+ᶻ (posᶻ (suc a)) (posᶻ      0 )  i = ℤ→Int (sucℤ (+-comm (pos a) 0 i))
  +ᵗʳ≡'+ᶻ (posᶻ (suc a)) (posᶻ (suc b))   =
    (posᶻ (suc a) +ᵗʳ posᶻ (suc b))  ≡⟨ sym (sucInt-preserves-ℤ→Int (signed spos a + signed spos (suc b))) ⟩
    sucInt (posᶻ a +ᵗʳ posᶻ (suc b)) ≡⟨ (λ i → sucInt $ (+ᵗʳ≡'+ᶻ (posᶻ a) (posᶻ (suc b)) ∙ sucInt+ (posᶻ a) (posᶻ b)) i) ⟩
    sucInt (posᶻ (suc a) +pos b)   ∎
  +ᵗʳ≡'+ᶻ (posᶻ      0 ) (negsucᶻ   b )   = sym (+negsuc-identityˡ b)
  +ᵗʳ≡'+ᶻ (posᶻ (suc a)) (negsucᶻ   b )   =
    (posᶻ (suc a) +ᵗʳ negsucᶻ b)  ≡⟨ sym $ sucInt-preserves-ℤ→Int (signed spos a + signed sneg (suc b)) ⟩
    sucInt (posᶻ a +ᵗʳ negsucᶻ b) ≡⟨ (λ i → sucInt $ +ᵗʳ≡'+ᶻ (posᶻ a) (negsucᶻ b) i) ⟩
    sucInt (posᶻ a +ᶻ  negsucᶻ b) ≡⟨ sucInt+ (posᶻ a) (negsucᶻ b) ⟩
    (posᶻ (suc a) +negsuc b)    ∎
  +ᵗʳ≡'+ᶻ (negsucᶻ   a ) (posᶻ      0 )   i = ℤ→Int $ -_ $  sucℤ $ -_ $ +-comm (signed sneg a) (pos 0) i
  +ᵗʳ≡'+ᶻ (negsucᶻ   a ) (posᶻ (suc b))   =
    (negsucᶻ a +ᵗʳ posᶻ (suc b))  ≡⟨ (λ i → ℤ→Int $ - sucℤ (- sucℤ-+ʳ (signed sneg a) (signed spos b) (~ i))) ⟩
    ℤ→Int (- sucℤ (- sucℤ (signed sneg a + signed spos b))) ≡⟨ (λ i → ℤ→Int $ -sucℤ-sucℤ≡sucℤ-sucℤ- (signed sneg a + signed spos b) i) ⟩
    ℤ→Int (sucℤ (- sucℤ (- (signed sneg a + signed spos b)))) ≡⟨ sym $ sucInt-preserves-ℤ→Int (- sucℤ (- (signed sneg a + signed spos b))) ⟩
    sucInt (negsucᶻ a +ᵗʳ posᶻ b) ≡⟨ (λ i → sucInt $ +ᵗʳ≡'+ᶻ (negsucᶻ a) (posᶻ b) i) ⟩
    sucInt (negsucᶻ a +pos b)   ∎
  +ᵗʳ≡'+ᶻ (negsucᶻ zero) (negsucᶻ b) = sym $ negsuc+negsuc≡+ⁿ 0 b
  +ᵗʳ≡'+ᶻ (negsucᶻ (suc a)) (negsucᶻ b) =
   (negsucᶻ (suc a) +ᵗʳ negsucᶻ b)   ≡⟨ sym $ predInt-preserves-ℤ→Int (- sucℤ (- (signed sneg a + signed sneg (suc b)))) ⟩
   predInt (negsucᶻ a +ᵗʳ negsucᶻ b) ≡⟨ (λ i → predInt $ +ᵗʳ≡'+ᶻ (negsucᶻ a) (negsucᶻ b) i) ⟩
   predInt (negsucᶻ a +ᶻ  negsucᶻ b) ≡⟨ predInt+ (negsucᶻ a) (negsucᶻ b) ⟩
   (negsucᶻ (suc a) +negsuc b)     ∎

  +ᵗʳ≡+ᶻ : _+ᵗʳ_ ≡ _+ᶻ_
  +ᵗʳ≡+ᶻ i a b = +ᵗʳ≡'+ᶻ a b i

+≡+ᶻ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _+_ _+ᶻ_
+≡+ᶻ = J (λ _+ᵗʳ_ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) _+_ _+ᵗʳ_) +≡+ᵗʳ +ᵗʳ≡+ᶻ

private
  -ᵗʳ_ : Int → Int
  -ᵗʳ_ = transport (λ i → (ℤ≡Int i → ℤ≡Int i)) -_

  -≡-ᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i)) -_ -ᵗʳ_
  -≡-ᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j)) (~ i) -_

  -ᵗʳ≡'-ᶻ : ∀ a → -ᵗʳ a ≡ -ᶻ a
  -ᵗʳ≡'-ᶻ (posᶻ zero) = refl
  -ᵗʳ≡'-ᶻ (posᶻ (suc n)) = refl
  -ᵗʳ≡'-ᶻ (negsucᶻ n) = refl

  -ᵗʳ≡-ᶻ : (-ᵗʳ_) ≡ (-ᶻ_)
  -ᵗʳ≡-ᶻ i a = -ᵗʳ≡'-ᶻ a i

-≡-ᶻ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i)) (-_) (-ᶻ_)
-≡-ᶻ = J (λ -ᵗʳ_ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i)) -_ -ᵗʳ_) -≡-ᵗʳ -ᵗʳ≡-ᶻ

min : ℤ → ℤ → ℤ
min x y with sign x | sign y
... | spos | spos = pos (minⁿ (abs x) (abs y))
... | spos | sneg = y
... | sneg | spos = x
... | sneg | sneg = neg (maxⁿ (abs x) (abs y))

max : ℤ → ℤ → ℤ
max x y with sign x | sign y
... | spos | spos = pos (maxⁿ (abs x) (abs y))
... | spos | sneg = x
... | sneg | spos = y
... | sneg | sneg = neg (minⁿ (abs x) (abs y))

private
  minᵗʳ : Int → Int → Int
  minᵗʳ = transport (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) min

  maxᵗʳ : Int → Int → Int
  maxᵗʳ = transport (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) max

  min≡minᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) min minᵗʳ
  min≡minᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j)) (~ i) min

  max≡maxᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) max maxᵗʳ
  max≡maxᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j)) (~ i) max

  minᵗʳ≡'minᶻ : ∀ a b → minᵗʳ a b ≡ minᶻ a b
  minᵗʳ≡'minᶻ (posᶻ      0 ) (posᶻ      0 ) = refl
  minᵗʳ≡'minᶻ (posᶻ      0 ) (posᶻ (suc b)) = refl
  minᵗʳ≡'minᶻ (posᶻ (suc a)) (posᶻ      0 ) = refl
  minᵗʳ≡'minᶻ (posᶻ (suc a)) (posᶻ (suc b)) = refl
  minᵗʳ≡'minᶻ (posᶻ      0 ) (negsucᶻ   b ) = refl
  minᵗʳ≡'minᶻ (posᶻ (suc a)) (negsucᶻ   b ) = refl
  minᵗʳ≡'minᶻ (negsucᶻ   a ) (posᶻ      0 ) = refl
  minᵗʳ≡'minᶻ (negsucᶻ   a ) (posᶻ (suc b)) = refl
  minᵗʳ≡'minᶻ (negsucᶻ   a ) (negsucᶻ   b ) = refl

  maxᵗʳ≡'maxᶻ : ∀ a b → maxᵗʳ a b ≡ maxᶻ a b
  maxᵗʳ≡'maxᶻ (posᶻ      0 ) (posᶻ      0 ) = refl
  maxᵗʳ≡'maxᶻ (posᶻ      0 ) (posᶻ (suc b)) = refl
  maxᵗʳ≡'maxᶻ (posᶻ (suc a)) (posᶻ      0 ) = refl
  maxᵗʳ≡'maxᶻ (posᶻ (suc a)) (posᶻ (suc b)) = refl
  maxᵗʳ≡'maxᶻ (posᶻ      0 ) (negsucᶻ   b ) = refl
  maxᵗʳ≡'maxᶻ (posᶻ (suc a)) (negsucᶻ   b ) = refl
  maxᵗʳ≡'maxᶻ (negsucᶻ   a ) (posᶻ      0 ) = refl
  maxᵗʳ≡'maxᶻ (negsucᶻ   a ) (posᶻ (suc b)) = refl
  maxᵗʳ≡'maxᶻ (negsucᶻ   a ) (negsucᶻ   b ) = refl

  minᵗʳ≡minᶻ : minᵗʳ ≡ minᶻ
  minᵗʳ≡minᶻ i a b = minᵗʳ≡'minᶻ a b i

  maxᵗʳ≡maxᶻ : maxᵗʳ ≡ maxᶻ
  maxᵗʳ≡maxᶻ i a b = maxᵗʳ≡'maxᶻ a b i

min≡min : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) min minᶻ
min≡min = J (λ minᵗʳ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) min minᵗʳ) min≡minᵗʳ minᵗʳ≡minᶻ

max≡max : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) max maxᶻ
max≡max = J (λ maxᵗʳ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i → ℤ≡Int i)) max maxᵗʳ) max≡maxᵗʳ maxᵗʳ≡maxᶻ

infixl 4 _<_
_<_ : ∀(x y : ℤ) → hProp ℓ-zero
x < y with sign x | sign y
... | spos | spos = abs x <ⁿ abs y
... | spos | sneg = ⊥
... | sneg | spos = ⊤
... | sneg | sneg = abs y <ⁿ abs x

private

  _<ᵗʳ_ : Int → Int → hProp ℓ-zero
  _<ᵗʳ_ = transport (λ i → (ℤ≡Int i → ℤ≡Int i → hProp ℓ-zero)) _<_

  <≡<ᵗʳ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → hProp ℓ-zero)) _<_ _<ᵗʳ_
  <≡<ᵗʳ i = transp (λ j → ℤ≡Int (i ∧ j) → ℤ≡Int (i ∧ j) → hProp ℓ-zero) (~ i) _<_

  <ᵗʳ⇔<ᶻ : ∀ a b → [ (a <ᵗʳ b) ⇔ (a <ᶻ b) ]
  <ᵗʳ⇔<ᶻ (posᶻ      0 ) (posᶻ      0 ) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ      0 ) (posᶻ (suc b)) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ (suc a)) (posᶻ      0 ) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ (suc a)) (posᶻ (suc b)) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ      0 ) (negsucᶻ   b ) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ (suc a)) (negsucᶻ   b ) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (posᶻ      0 ) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (posᶻ (suc b)) .fst pᵗʳ = pᵗʳ
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (negsucᶻ   b ) .fst pᵗʳ = sucⁿ-creates-<ⁿ b a .snd pᵗʳ
  <ᵗʳ⇔<ᶻ (posᶻ      0 ) (posᶻ      0 ) .snd p  = p
  <ᵗʳ⇔<ᶻ (posᶻ      0 ) (posᶻ (suc b)) .snd p  = p
  <ᵗʳ⇔<ᶻ (posᶻ (suc a)) (posᶻ      0 ) .snd p  = p
  <ᵗʳ⇔<ᶻ (posᶻ (suc a)) (posᶻ (suc b)) .snd p  = p
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (posᶻ      0 ) .snd p  = p
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (posᶻ (suc b)) .snd p  = p
  <ᵗʳ⇔<ᶻ (negsucᶻ   a ) (negsucᶻ   b ) .snd p  = sucⁿ-creates-<ⁿ b a .fst p

  <ᵗʳ≡<ᶻ : _<ᵗʳ_ ≡ _<ᶻ_
  <ᵗʳ≡<ᶻ i a b = ⇔toPath {P = a <ᵗʳ b} {Q = a <ᶻ b} (<ᵗʳ⇔<ᶻ a b .fst) (<ᵗʳ⇔<ᶻ a b .snd) i

<≡<ᶻ : PathP (λ i → (ℤ≡Int i → ℤ≡Int i → hProp ℓ-zero)) _<_ _<ᶻ_
<≡<ᶻ = J (λ _<ᵗʳ_ _ → PathP (λ i → (ℤ≡Int i → ℤ≡Int i → hProp ℓ-zero)) _<_ _<ᵗʳ_) <≡<ᵗʳ <ᵗʳ≡<ᶻ

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _·_ -_ _<_ min max ]
is-LinearlyOrderedCommRing = transport γ is-LinearlyOrderedCommRingᶻ where
  γ : ([ isLinearlyOrderedCommRing 0 1 _+ᶻ_ _·ᶻ_ (-ᶻ_) _<ᶻ_ minᶻ maxᶻ ])
    ≡ [ isLinearlyOrderedCommRing 0 1 _+_ _·_ -_ _<_ min max ]
  γ i = [ isLinearlyOrderedCommRing 0ⁱ 1ⁱ _+ⁱ_ _·ⁱ_ -ⁱ_ _<ⁱ_ minⁱ maxⁱ ] where
    0ⁱ = transport (λ j → ℤ≡Int (~ i ∧ j)) 0
    1ⁱ = transport (λ j → ℤ≡Int (~ i ∧ j)) 1
    _+ⁱ_ = +≡+ᶻ (~ i)
    _·ⁱ_ = ·≡·ᶻ (~ i)
    -ⁱ_  = -≡-ᶻ (~ i)
    _<ⁱ_ = <≡<ᶻ (~ i)
    minⁱ = min≡min (~ i)
    maxⁱ = max≡max (~ i)

bundle : LinearlyOrderedCommRing {ℓ-zero} {ℓ-zero}
bundle .LinearlyOrderedCommRing.Carrier                    = ℤ
bundle .LinearlyOrderedCommRing.0f                         = 0
bundle .LinearlyOrderedCommRing.1f                         = 1
bundle .LinearlyOrderedCommRing._+_                        = _+_
bundle .LinearlyOrderedCommRing._·_                        = _·_
bundle .LinearlyOrderedCommRing.-_                         = -_
bundle .LinearlyOrderedCommRing.min                        = min
bundle .LinearlyOrderedCommRing.max                        = max
bundle .LinearlyOrderedCommRing._<_                        = _<_
bundle .LinearlyOrderedCommRing.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing

·-reflects-< : (x y z : ℤ) → [ 0 < z ] → [ (x · z) < (y · z) ] → [ x < y ]
·-reflects-< = transport γ ·ᶻ-reflects-<ᶻ where
  γ : ((x y z : Int) → [ 0 <ᶻ z ] → [  x ·ᶻ z  <ᶻ  y ·ᶻ z  ] → [ x <ᶻ y ])
    ≡ ((x y z :   ℤ) → [ 0 < z ] → [ (x · z) < (y · z) ] → [ x < y ])
  γ i = let _·'_ = ·≡·ᶻ (~ i); _<'_ = <≡<ᶻ (~ i); 0ⁱ = transport (λ j → ℤ≡Int (~ i ∧ j)) 0 in
      ((x y z :    ℤ≡Int (~ i)) → [ 0ⁱ <' z ] → [ (x ·' z) <' (y ·' z) ] → [ x <' y ])
