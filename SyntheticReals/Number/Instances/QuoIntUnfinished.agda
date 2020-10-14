{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Instances.QuoInt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (not)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)

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

open import SyntheticReals.Number.Instances.Nat using (lemma10''; lemma12'') renaming
  ( _<_ to _<ⁿ_
  ; <-irrefl  to <ⁿ-irrefl
  ; <-cotrans to <ⁿ-cotrans
  ; suc-creates-< to sucⁿ-creates-<ⁿ
  ; 0<suc to 0<ⁿsuc
  )
open import Data.Nat.Base using () renaming
  ( _⊔_ to maxⁿ
  ; _⊓_ to minⁿ
  ; _+_ to _+ⁿ_
  )

open import Cubical.HITs.Ints.QuoInt
open import Cubical.HITs.Ints.QuoInt.Properties
open import Cubical.Data.Nat using (suc; zero; ℕ) renaming
  ( +-comm to +ⁿ-comm )
open import Cubical.Data.Nat.Order using () renaming
  ( <-trans to <ⁿ-trans
  ; _<_ to _<ⁿᵗ_
  ; _≟_ to _≟ⁿ_
  ; lt to ltⁿ
  ; gt to gtⁿ
  ; eq to eqⁿ
  ; ¬-<-zero to ¬-<ⁿ-zero
  )

-- hProp-valued _<_
_<_ : ∀(x y : ℤ) → hProp ℓ-zero
x < y with sign x | sign y
... | spos | spos = abs x <ⁿ abs y
... | spos | sneg = ⊥
... | sneg | spos = ⊤ -- ↯ NOTE: exploiting this specific behaviour of `sign` is not much different from using just `Int`
... | sneg | sneg = abs y <ⁿ abs x

-- _<_ on a representation `λ x → (sign x , abs x)` of QuoInt
_<ʳ_ : ∀(x y : Sign × ℕ) → hProp ℓ-zero
(spos , x) <ʳ (spos , y) = x <ⁿ y
(spos , x) <ʳ (sneg , y) = ⊥
(sneg , x) <ʳ (spos , y) = ⊤
(sneg , x) <ʳ (sneg , y) = y <ⁿ x

<≡<ʳ : ∀ x y → x < y ≡ (sign x , abs x) <ʳ (sign y , abs y)
<≡<ʳ x y with sign x | sign y
... | spos | spos = refl
... | spos | sneg = refl
... | sneg | spos = refl
... | sneg | sneg = refl

-- different version of _<_
_<'_ : ℤ → ℤ → hProp ℓ-zero
pos      n₀  <' pos      n₁  = n₀ <ⁿ n₁
pos      n₀  <' neg      n₁  = ⊥
neg      0   <' pos      0   = ⊥
neg      0   <' pos (suc n₁) = ⊤
neg (suc n₀) <' pos      0   = ⊤
neg (suc n₀) <' pos (suc n₁) = ⊤
neg      n₀  <' neg      n₁  = n₁ <ⁿ n₀
pos      n₀  <' posneg   j   = lemma10'' n₀    j
neg      0   <' posneg   j   = lemma10'' 0  (~ j)
neg (suc n₀) <' posneg   j   = lemma12'' n₀ (~ j)
posneg   i   <' pos      0   = lemma10'' 0     i
posneg   i   <' pos (suc n₁) = lemma12'' n₁    i
posneg   i   <' neg      n₁  = lemma10'' n₁ (~ i)
posneg   i   <' posneg   j   = lemma10'' 0 ((i ∨ j) ∧ ~(i ∧ j))

<'≡< : ∀ x y → x <' y ≡ x < y
<'≡< (pos  zero  ) (pos  zero  ) = refl
<'≡< (pos  zero  ) (pos (suc y)) = refl
<'≡< (pos (suc x)) (pos  zero  ) = refl
<'≡< (pos (suc x)) (pos (suc y)) = refl
<'≡< (pos  zero  ) (neg  zero  ) = sym (lemma10'' _)
<'≡< (pos  zero  ) (neg (suc y)) = refl
<'≡< (pos (suc x)) (neg  zero  ) = sym (lemma10'' _)
<'≡< (pos (suc x)) (neg (suc y)) = refl
<'≡< (neg  zero  ) (pos  zero  ) = sym (lemma10'' _)
<'≡< (neg  zero  ) (pos (suc y)) = sym (lemma12'' _)
<'≡< (neg (suc x)) (pos  zero  ) = refl
<'≡< (neg (suc x)) (pos (suc y)) = refl
<'≡< (neg  zero  ) (neg  zero  ) = refl
<'≡< (neg  zero  ) (neg (suc y)) = lemma10'' _
<'≡< (neg (suc x)) (neg  zero  ) = lemma12'' _
<'≡< (neg (suc x)) (neg (suc y)) = refl
<'≡< (pos  zero  ) (posneg i) j = lemma10'' 0 (~ j ∧ i)
<'≡< (pos (suc x)) (posneg i) j = lemma10'' (suc x) (~ j ∧ i)
<'≡< (neg  zero  ) (posneg i) j = lemma10'' 0 (~ j ∧ ~ i)
<'≡< (neg (suc x)) (posneg i) j = lemma12'' x (j ∨ ~ i)
<'≡< (posneg i) (pos  zero  ) j = lemma10'' 0 (~ j ∧ i)
<'≡< (posneg i) (pos (suc y)) j = lemma12'' y (~ j ∧ i)
<'≡< (posneg i) (neg  zero  ) j = lemma10'' 0 (~ j ∧ ~ i)
<'≡< (posneg i) (neg (suc y)) j = lemma10'' (suc y) (j ∨ ~ i)
<'≡< (posneg i) (posneg   j ) k = lemma10'' 0 (((i ∨ j) ∧ ~ i ∨ ~ j) ∧ ~ k)

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

<-irrefl : (a : ℤ) → [ ¬ (a < a) ]
<-irrefl (pos zero)    = <ⁿ-irrefl 0
<-irrefl (pos (suc n)) = <ⁿ-irrefl (suc n)
<-irrefl (neg zero)    = <ⁿ-irrefl 0
<-irrefl (neg (suc n)) = <ⁿ-irrefl (suc n)
<-irrefl (posneg i) p  = <ⁿ-irrefl 0 p

<-trans : (a b c : ℤ) → [ a < b ] → [ b < c ] → [ a < c ]
<-trans a b c a<b b<c with sign a | sign b | sign c
  | pathTo⇒ (<≡<ʳ a b) a<b
  | pathTo⇒ (<≡<ʳ b c) b<c
  | pathTo⇐ (<≡<ʳ a c)
... | spos | spos | spos | a<b' | b<c' | p = p (<ⁿ-trans a<b' b<c')
... | spos | spos | sneg | a<b' | b<c' | p = p b<c'
... | spos | sneg | spos | a<b' | b<c' | p = p (⊥-elim a<b')
... | spos | sneg | sneg | a<b' | b<c' | p = p a<b'
... | sneg | spos | spos | a<b' | b<c' | p = p a<b'
... | sneg | spos | sneg | a<b' | b<c' | p = p (⊥-elim b<c')
... | sneg | sneg | spos | a<b' | b<c' | p = p b<c'
... | sneg | sneg | sneg | a<b' | b<c' | p = p (<ⁿ-trans b<c' a<b')

<-cotrans : (a b : ℤ) → [ a < b ] → (x : ℤ) → [ (a < x) ⊔ (x < b) ]
<-cotrans a b a<b c with sign a , abs a | sign b , abs b | sign c , abs c
  | pathTo⇒ (<≡<ʳ a b) a<b
  | pathTo⇐ (λ i → (<≡<ʳ a c) i ⊔ (<≡<ʳ c b) i)
... | spos , a' | spos , b' | spos , c' | a<b' | p = p (<ⁿ-cotrans _ _ a<b' c')
... | spos , a' | spos , b' | sneg , c' | a<b' | p = p (inrᵖ tt)
... | sneg , a' | spos , b' | spos , c' | a<b' | p = p (inlᵖ tt)
... | sneg , a' | spos , b' | sneg , c' | a<b' | p = p (inrᵖ tt)
... | sneg , a' | sneg , b' | spos , c' | a<b' | p = p (inlᵖ tt)
... | sneg , a' | sneg , b' | sneg , c' | a<b' | p = p (pathTo⇒ (⊔-comm (b' <ⁿ c') (c' <ⁿ a')) (<ⁿ-cotrans _ _ a<b' c'))

data Trichotomy (m n : ℤ) : Type₀ where
  lt : [ m < n ] → Trichotomy m n
  eq :   m ≡ n   → Trichotomy m n
  gt : [ n < m ] → Trichotomy m n

record Reveal'_·_is_ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                   (f⁻¹ : B → A)
                   (y : B) (x : A)
                   : Type ℓ where
  eta-equality
  constructor [_]ⁱ'
  field eq' : x ≡ f⁻¹ y

inspect' : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
          (f⁻¹ : B → A) (f : A → B) (x : A) → f⁻¹ (f x) ≡ x → Reveal' f⁻¹ · (f x) is x
inspect' f⁻¹ f x p = [ sym p ]ⁱ'

reprℤ : ℤ → Sign × ℕ
reprℤ z = sign z , abs z

reprℤ⁻¹ : Sign × ℕ → ℤ
reprℤ⁻¹ (s , n) = signed s n

reprℤ-id : ∀ z → reprℤ⁻¹ (reprℤ z) ≡ z
reprℤ-id (pos  zero  ) = refl
reprℤ-id (pos (suc n)) = refl
reprℤ-id (neg  zero  ) = posneg
reprℤ-id (neg (suc n)) = refl
reprℤ-id (posneg   i ) = λ j → posneg (i ∧ j)

inspect-reprℤ : (x : ℤ) → Reveal' reprℤ⁻¹ · (reprℤ x) is x
inspect-reprℤ a = inspect' reprℤ⁻¹ reprℤ a (reprℤ-id a)

-- abs : ℤ → ℕ
-- abs (signed _ n) = n
-- abs (posneg i) = zero

-- NOTE: this would be easier to get from `Int≡QuoInt`
_≟_ : ∀ m n → Trichotomy m n
m ≟ n with reprℤ m | reprℤ n
  | inspect-reprℤ m
  | inspect-reprℤ n
  | abs m ≟ⁿ abs n
  | pathTo⇐ (<≡<ʳ m n)
  | pathTo⇐ (<≡<ʳ n m)
... | spos , m' | spos , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | ltⁿ x | p | q = lt (p (transport (λ i → [ abs (m≡ i) <ⁿ abs (n≡ i) ]) x))
... | spos , m' | spos , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | eqⁿ x | p | q = let m'≡n' = (λ i → abs (m≡ (~ i))) ∙ x ∙ (λ i → abs (n≡ i))
                                                                    in eq (transport (λ i → (m≡ (~ i)) ≡ (n≡ (~ i))) (λ i → pos (m'≡n' i)))
... | spos , m' | spos , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | gtⁿ x | p | q = gt (q (transport (λ i → [ abs (n≡ i) <ⁿ abs (m≡ i) ]) x))
... | spos , m' | sneg , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | o     | p | q = gt (q tt)
... | sneg , m' | spos , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | o     | p | q = lt (p tt)
... | sneg , m' | sneg , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | ltⁿ x | p | q = gt (q (transport (λ i → [ abs (m≡ i) <ⁿ abs (n≡ i) ]) x))
... | sneg , m' | sneg , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | eqⁿ x | p | q = let m'≡n' = (λ i → abs (m≡ (~ i))) ∙ x ∙ (λ i → abs (n≡ i))
                                                                    in eq (transport (λ i → (m≡ (~ i)) ≡ (n≡ (~ i))) (λ i → neg (m'≡n' i)))
... | sneg , m' | sneg , n' | [ m≡ ]ⁱ' | [ n≡ ]ⁱ' | gtⁿ x | p | q = lt (p (transport (λ i → [ abs (n≡ i) <ⁿ abs (m≡ i) ]) x))

is-min : (x y z : ℤ) → [ ¬ᵖ (min x y < z) ⇔ ¬ᵖ (x < z) ⊓ ¬ᵖ (y < z) ]
is-min = {!  !}

is-max : (x y z : ℤ) → [ ¬ᵖ (z < max x y) ⇔ ¬ᵖ (z < x) ⊓ ¬ᵖ (z < y) ]
is-max = {!  !}

sucℤ-pos-suc : ∀ n → sucℤ (pos n) ≡ pos (suc n)
sucℤ-pos-suc x = refl -- holds definitionally

+-preserves-pos : ∀ x y → pos x + pos y ≡ pos (x +ⁿ y)
+-preserves-pos zero y = refl
+-preserves-pos (suc x) zero = transport (λ i → sucℤ (+-comm (pos 0) (pos x) i) ≡ pos (suc (+ⁿ-comm 0 x i))) refl
+-preserves-pos (suc x) (suc y) = λ i → sucℤ (+-preserves-pos x (suc y) i)

-- +-reflects-< : ∀ a b x → [ (a + x) < (b + x) ] → [ a < b ]
-- +-reflects-< a b x a+x<b+x with reprℤ a | reprℤ b | reprℤ x | reprℤ (a + x) | reprℤ (b + x)
--   | inspect-reprℤ a
--   | inspect-reprℤ b
--   | inspect-reprℤ x
--   | inspect-reprℤ (a + x)
--   | inspect-reprℤ (b + x)
--   | pathTo⇒ (<≡<ʳ (a + x) (b + x)) a+x<b+x
--   | pathTo⇐ (<≡<ʳ a b)
-- ... | spos , a' | spos , b' | sx , x' | spos , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | spos , a' | spos , b' | sx , x' | sneg , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | spos , a' | spos , b' | sx , x' | sneg , a+x | sneg , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | spos , a' | sneg , b' | sx , x' | spos , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | spos , a' | sneg , b' | sx , x' | sneg , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | spos , a' | sneg , b' | sx , x' | sneg , a+x | sneg , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | spos , b' | sx , x' | spos , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | spos , b' | sx , x' | sneg , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | spos , b' | sx , x' | sneg , a+x | sneg , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | sneg , b' | sx , x' | spos , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | sneg , b' | sx , x' | sneg , a+x | spos , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}
-- ... | sneg , a' | sneg , b' | sx , x' | sneg , a+x | sneg , b+x | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | [ x≡ ]ⁱ' | [ a+x≡ ]ⁱ' | [ b+x≡ ]ⁱ' | p | q = q {!   !}

+-identity-posˡ : ∀ a → pos zero + a ≡ a
+-identity-posˡ a = refl

+-identity-posʳ : ∀ a → a + pos zero ≡ a
+-identity-posʳ a = +-comm a (pos zero) ∙ +-identity-posˡ a

-- -_ : ℤ → ℤ
-- - signed s n = signed (not s) n
-- - posneg i   = posneg (~ i)
--
-- _+_ : ℤ → ℤ → ℤ
-- (signed _ zero) + n = n
-- (posneg _)      + n = n
-- (pos (suc m))   + n = sucℤ  (pos m + n)
-- (neg (suc m))   + n = predℤ (neg m + n)

pos≡-neg : ∀ n → pos n ≡ - neg n
pos≡-neg n = refl

-pos≡neg : ∀ n → - pos n ≡ neg n
-pos≡neg n = refl

suc-neg-suc≡neg : ∀ n → sucℤ (neg (suc n)) ≡ neg n
suc-neg-suc≡neg n = refl

pos+neg≡0 : ∀ n → pos n + neg n ≡ 0
pos+neg≡0 zero = sym posneg
pos+neg≡0 (suc n) = transport (
  pos n + neg n                ≡ pos 0 ≡⟨ (λ i → +-comm (pos n) (neg n) i ≡ pos 0) ⟩
  neg n + pos n                ≡ pos 0 ≡⟨ refl ⟩
  (sucℤ (neg (suc n)) + pos n) ≡ pos 0 ≡⟨ (λ i → sucℤ-+ˡ (neg (suc n)) (pos n) (~ i) ≡ pos 0) ⟩
  sucℤ (neg (suc n) + pos n)   ≡ pos 0 ≡⟨ (λ i → sucℤ (+-comm (pos n) (neg (suc n)) (~ i)) ≡ pos 0) ⟩
  sucℤ (pos n + neg (suc n))   ≡ pos 0 ∎) (pos+neg≡0 n)

neg+pos≡0 : ∀ n → neg n + pos n ≡ 0
neg+pos≡0 n = +-comm (neg n) (pos n) ∙ pos+neg≡0 n

+-inverseʳ : ∀ a → a + (- a) ≡ 0
+-inverseʳ a with reprℤ a | inspect-reprℤ a
... | spos , a' | [ a≡ ]ⁱ' = transport (λ i → a≡ (~ i) + (- a≡ (~ i)) ≡ pos 0) (pos+neg≡0 a')
... | sneg , a' | [ a≡ ]ⁱ' = transport (λ i → a≡ (~ i) + (- a≡ (~ i)) ≡ pos 0) (neg+pos≡0 a')

+-inverseˡ : ∀ a → (- a) + a ≡ 0
+-inverseˡ a = +-comm (- a) a ∙ +-inverseʳ a

+-inverse : (x : ℤ) → (x + (- x) ≡ pos 0) × ((- x) + x ≡ pos 0)
+-inverse x .fst = +-inverseʳ x
+-inverse x .snd = +-inverseˡ x

-- -on-reprℤ : ∀ a → (sign (- a) , abs (- a)) ≡ (not (sign a) , abs a)
-- -on-reprℤ (pos zero) = {!   !} -- Goal (spos , 0) ≡ (sneg , 0)
-- -on-reprℤ (pos (suc n)) = {!   !}
-- -on-reprℤ (neg n) = {!   !}
-- -on-reprℤ (posneg i) = {!   !}

-flips-< : ∀ a b → [ a < b ] → [ (- b) < (- a) ]
-flips-< a b a<b with reprℤ a | reprℤ b
  | inspect-reprℤ a
  | inspect-reprℤ b
  | pathTo⇒ (<≡<ʳ a b) a<b
  | pathTo⇐ (<≡<ʳ (- b) (- a))
... | spos , zero   | spos , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r p)
... | sneg , zero   | spos , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r (⊥-elim $ <-irrefl a $ subst (λ p → [ a < p ]) (b≡ ∙ posneg ∙ sym a≡) a<b))
... | sneg , zero   | sneg , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r p)
... | spos , zero   | spos , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r tt)
... | sneg , zero   | spos , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r tt)
... | sneg , zero   | sneg , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r p)
... | spos , suc a' | spos , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r (¬-<ⁿ-zero p))
... | sneg , suc a' | spos , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r (0<ⁿsuc _))
... | sneg , suc a' | sneg , zero   | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r (0<ⁿsuc _))
... | spos , suc a' | spos , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r p)
... | sneg , suc a' | spos , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r tt)
... | sneg , suc a' | sneg , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (sym λ i → fst ((sign (- b≡ i) , abs (- b≡ i)) <ʳ (sign (- a≡ i) , abs (- a≡ i)))) in q (r p)

-- suc-reflects-< : ∀ a b → [ sucℤ a < sucℤ b ] → [ a < b ]
-- suc-reflects-< (pos zero) (pos zero) sa<sb = ⊥-elim $ <-irrefl (pos 1) sa<sb
-- suc-reflects-< (pos zero) (pos (suc n₁)) sa<sb = sucⁿ-creates-<ⁿ 0 (suc n₁) .snd sa<sb
-- suc-reflects-< (pos zero) (neg zero) sa<sb = {!   !}
-- suc-reflects-< (pos zero) (neg (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (pos (suc n₀)) (pos zero) sa<sb = {!   !}
-- suc-reflects-< (pos (suc n₀)) (pos (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (pos (suc n₀)) (neg zero) sa<sb = {!   !}
-- suc-reflects-< (pos (suc n₀)) (neg (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (neg zero) (pos zero) sa<sb = {!   !}
-- suc-reflects-< (neg zero) (pos (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (neg zero) (neg zero) sa<sb = {!   !}
-- suc-reflects-< (neg zero) (neg (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (neg (suc n₀)) (pos zero) sa<sb = {!   !}
-- suc-reflects-< (neg (suc n₀)) (pos (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (neg (suc n₀)) (neg zero) sa<sb = {!   !}
-- suc-reflects-< (neg (suc n₀)) (neg (suc n₁)) sa<sb = {!   !}
-- suc-reflects-< (signed s₀ n₀) (posneg j) sa<sb = {!   !}
-- suc-reflects-< (posneg i) (signed s₁ n₁) sa<sb = {!   !}
-- suc-reflects-< (posneg i) (posneg j) sa<sb = {!   !}

suc-reflects-< : ∀ a b → [ sucℤ a < sucℤ b ] → [ a < b ]
suc-reflects-< a b sa<sb with reprℤ a | reprℤ b
  | inspect-reprℤ a
  | inspect-reprℤ b
  | pathTo⇒ (<≡<ʳ (sucℤ a) (sucℤ b)) sa<sb
  | pathTo⇐ (<≡<ʳ a b)
... | spos , a' | spos , b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
                                                          in q (sucⁿ-creates-<ⁿ a' b' .snd r)
-- ... | spos , a' | sneg , b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
--                                                           in q {!  !}
... | spos , a' | sneg , 0 | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
                                                          in q (¬-<ⁿ-zero $ sucⁿ-creates-<ⁿ a' 0 .snd r)
... | spos , a' | sneg , suc 0 | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
                                                          in q (¬-<ⁿ-zero r)
... | spos , a' | sneg , suc (suc b') | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
                                                          in q r
... | sneg , a' | spos , b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = q tt
... | sneg , zero | sneg , zero | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = q (⊥-elim $ <-irrefl (sucℤ a) $ subst (λ p → [ sucℤ a < sucℤ p ]) (b≡ ∙ sym a≡) sa<sb)
... | sneg , zero | sneg , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = q {!   !}
... | sneg , suc a' | sneg , zero | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = q (0<ⁿsuc _)
... | sneg , suc a' | sneg , suc b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (sign (sucℤ (a≡ i)) , abs (sucℤ (a≡ i))) <ʳ (sign (sucℤ (b≡ i)) , abs (sucℤ (b≡ i))) ]) p
                                                                    in q {!   !}
-- ... | sneg , a' | sneg , b' | [ a≡ ]ⁱ' | [ b≡ ]ⁱ' | p | q = let r = transport (λ i → [ (- sucℤ (b≡ i)) < (- sucℤ (a≡ i)) ] )
                                                          -- in q {!  sa<sb  !}

-- [ (a + pos (suc n)) < (b + pos (suc n)) ] →

+-reflects-< : ∀ a b x → [ (a + x) < (b + x) ] → [ a < b ]
+-reflects-< a b (pos (suc n)) a+x<b+x = +-reflects-< a b (pos n) {!   !}
+-reflects-< a b (neg (suc n)) a+x<b+x = {!   !}
-- +-reflects-< a b (pos zero) a+x<b+x = pathTo⇒ (λ i → +-identity-posʳ a i < +-identity-posʳ b i) a+x<b+x
+-reflects-< a b (pos zero) a+x<b+x = pathTo⇒ (λ i → +-comm a (pos zero) i < +-comm b (pos zero) i) a+x<b+x
+-reflects-< a b (neg zero) a+x<b+x = pathTo⇒ (λ i → +-comm a (neg zero) i < +-comm b (neg zero) i) a+x<b+x
+-reflects-< a b (posneg i) a+x<b+x = pathTo⇒ (λ j → +-comm a (posneg i) j < +-comm b (posneg i) j) a+x<b+x

+-<-ext : (w x y z : ℤ) → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
+-<-ext w x y z r with w ≟ y | x ≟ z
... | lt w<y | q = inlᵖ w<y
... | eq w≡y | q = inrᵖ {! +-injˡ y x z   !}
... | gt y<w | q = {!   !}

·-preserves-< : (x y z : ℤ) → [ 0 < z ] → [ x < y ] → [ (x * z) < (y * z) ]
·-preserves-< = {!  !}

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℤ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _*_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℤ
·-Semigroup .IsSemigroup.is-assoc = *-assoc

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-identityʳ x , refl

·-Monoid : [ isMonoid 1 _*_ ]
·-Monoid .IsMonoid.is-Semigroup = ·-Semigroup
·-Monoid .IsMonoid.is-identity x = *-identityʳ x , *-identityˡ x

is-Semiring : [ isSemiring 0 1 _+_ _*_ ]
is-Semiring .IsSemiring.+-Monoid = +-Monoid
is-Semiring .IsSemiring.·-Monoid = ·-Monoid
is-Semiring .IsSemiring.+-comm   = +-comm
is-Semiring .IsSemiring.is-dist x y z = sym (*-distribˡ x y z) , sym (*-distribʳ x y z)

is-CommSemiring : [ isCommSemiring 0 1 _+_ _*_ ]
is-CommSemiring .IsCommSemiring.is-Semiring = is-Semiring
is-CommSemiring .IsCommSemiring.·-comm      = *-comm

<-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = <-irrefl
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  a b c = <-trans a b c
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho a b with a ≟ b
... | lt a<b = inl (inl a<b)
... | eq a≡b = inr ∣ a≡b ∣
... | gt b<a = inl (inr b<a)

≤-isLattice : [ isLattice (λ x y → ¬ᵖ (y < x)) min max ]
≤-isLattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-isLattice .IsLattice.is-min         = is-min
≤-isLattice .IsLattice.is-max         = is-max

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _*_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-isLattice         = ≤-isLattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = +-<-ext
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = ·-preserves-<

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.+-inverse                      = +-inverse

ℤbundle : LinearlyOrderedCommRing {ℓ-zero} {ℓ-zero}
ℤbundle .LinearlyOrderedCommRing.Carrier                    = ℤ
ℤbundle .LinearlyOrderedCommRing.0f                         = 0
ℤbundle .LinearlyOrderedCommRing.1f                         = 1
ℤbundle .LinearlyOrderedCommRing._+_                        = _+_
ℤbundle .LinearlyOrderedCommRing._·_                        = _*_
ℤbundle .LinearlyOrderedCommRing.-_                         = -_
ℤbundle .LinearlyOrderedCommRing.min                        = min
ℤbundle .LinearlyOrderedCommRing.max                        = max
ℤbundle .LinearlyOrderedCommRing._<_                        = _<_
ℤbundle .LinearlyOrderedCommRing.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing
