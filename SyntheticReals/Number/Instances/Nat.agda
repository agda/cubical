{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Instances.Nat where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
-- open import Cubical.Structures.Ring
-- open import Cubical.Structures.Group
-- open import Cubical.Structures.AbGroup

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
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


open import Cubical.Data.Nat as Nat renaming (_*_ to _·_) hiding (min)
open import Cubical.Data.Nat.Order renaming (_<_ to _<ᵗ_)
open import Cubical.Data.Nat.Properties using
  ( inj-*sm
  ; inj-sm*
  ) renaming
  ( *-distribʳ  to ·-distribʳ
  ; *-distribˡ  to ·-distribˡ
  ; *-assoc     to ·-assoc
  ; *-comm      to ·-comm
  ; *-identityʳ to ·-identityʳ
  ; *-identityˡ to ·-identityˡ
  )
-- open import Data.Nat.Properties using (+-assoc)
open import Data.Nat.Base using () renaming
  ( _⊔_ to max
  ; _⊓_ to min
  )

-- _<_ as an hProp-valued relation
_<_ : (x y : ℕ) → hProp ℓ-zero
(x < y) .fst = x <ᵗ y
(x < y) .snd (k₁ , k₁+sx≡y) (k₂ , k₂+sx≡y) = φ where
  abstract φ = Σ≡Prop (λ k → isSetℕ _ _) (inj-+m (k₁+sx≡y ∙ sym k₂+sx≡y))

0<suc : ∀ a → 0 <ᵗ suc a
0<suc a = a , +-comm a 1

·-nullifiesˡ : ∀ x → 0 · x ≡ 0
·-nullifiesˡ x = refl

·-nullifiesʳ : ∀ x → x · 0 ≡ 0
·-nullifiesʳ zero = refl
·-nullifiesʳ (suc x) = ·-nullifiesʳ x

abstract
  lemma10   : ∀ n → (n <ᵗ 0) ≡ [ ⊥ ]
  lemma10   n = isoToPath (iso (λ{ (k , p) → snotz (sym (+-suc k n) ∙ p) }) ⊥-elim (λ b → isProp⊥ _ _) (λ a → isProp[] (n < 0) _ _))

  lemma10'' : ∀ n → (n < 0) ≡ ⊥
  lemma10'' n = ⇔toPath (transport (lemma10 n)) (transport (sym (lemma10 n)))

  lemma12 : ∀ n → [ 0 < suc n ] ≡ [ ⊤ ]
  lemma12 n = isoToPath (iso (λ _ →  tt) (λ _ → n , +-suc n 0 ∙ (λ i → suc (+-zero n i))) (λ b → isProp⊤ _ _) (λ a → isProp[] (0 < suc n) _ _))

  lemma12'' : ∀ n → (0 < suc n) ≡ ⊤
  lemma12'' n = ⇔toPath (transport (lemma12 n)) (transport (sym (lemma12 n)))

abstract
  <-irrefl       : (a       : ℕ) → [ ¬ (a < a) ]
  <-irrefl zero q = transp (λ i → [ lemma10'' 0 i ]) i0 q
  <-irrefl (suc a) (k , p) =
    snotz (inj-m+ {a} (+-suc a k ∙ (λ i → suc (+-comm a k i)) ∙ sym (+-suc k a) ∙ inj-m+ {1} (sym (+-suc k (suc a)) ∙ p) ∙ sym (+-zero a)))

  suc-creates-< : ∀ a b → [ a < b ⇔ suc a < suc b ]
  suc-creates-< a b .fst (k , p) = k , (+-suc k (suc a)) ∙ (λ i → suc (p i))
  suc-creates-< a b .snd (k , p) = k , inj-m+ {1} (sym (+-suc k (suc a)) ∙ p)

  +-createsˡ-< : ∀ a b x → [ a < b ⇔ (x + a) < (x + b) ]
  +-createsˡ-< a b  zero   .fst a<b = a<b
  +-createsˡ-< a b (suc x) .fst a<b = suc-creates-< (x + a) (x + b) .fst $ +-createsˡ-< a b x .fst a<b
  +-createsˡ-< a b zero .snd a<b = a<b
  +-createsˡ-< a b (suc x) .snd p = +-createsˡ-< a b x .snd (suc-creates-< (x + a) (x + b) .snd p)

  +-createsʳ-< : ∀ a b x → [ a < b ⇔ (a + x) < (b + x) ]
  +-createsʳ-< a b x .fst p = transport (λ i → [ +-comm x a i < +-comm x b i ]) $ +-createsˡ-< a b x .fst p
  +-createsʳ-< a b x .snd p = +-createsˡ-< a b x .snd (transport (λ i → [ +-comm a x i < +-comm b x i ]) p)

  <-cotrans      : (a b     : ℕ) → [ a < b ] → (x : ℕ) → [ (a < x) ⊔ (x < b) ]
  <-cotrans  zero    zero        q      c  = ⊥-elim {A = λ _ → [ (zero < c) ⊔ (c < zero) ]}  (<-irrefl _ q)
  <-cotrans  zero   (suc b)      q  zero   = inrᵖ q
  <-cotrans  zero   (suc b)      q (suc c) = inlᵖ (c , +-comm c 1)
  <-cotrans (suc a)  zero   (k , p)     c  = ⊥-elim {A = λ _ → [ (suc a < c) ⊔ (c < zero) ]} (snotz (sym (+-suc k (suc a)) ∙ p))
  <-cotrans (suc a) (suc b)      q  zero   = inrᵖ (b , +-comm b 1)
  <-cotrans (suc a) (suc b)      q (suc c) = transport (λ i → [ r i ⊔ s i ]) (<-cotrans a b (suc-creates-< a b .snd q) c)
    where r : (a < c) ≡ (suc a < suc c)
          s : (c < b) ≡ (suc c < suc b)
          r = ⇔toPath (suc-creates-< a c .fst) (suc-creates-< a c .snd)
          s = ⇔toPath (suc-creates-< c b .fst) (suc-creates-< c b .snd)

·-reflects-≡ʳ : ∀ a b x → [ 0 < x ] → a · x ≡ b · x → a ≡ b
·-reflects-≡ʳ a b zero    p q = ⊥-elim {A = λ _ → a ≡ b} $ <-irrefl 0 p
·-reflects-≡ʳ a b (suc x) p q = inj-*sm {l = a} {m = x} {n = b} q

·-reflects-≡ˡ : ∀ a b x → [ 0 < x ] → x · a ≡ x · b → a ≡ b
·-reflects-≡ˡ a b zero    p q = ⊥-elim {A = λ _ → a ≡ b} $ <-irrefl 0 p
·-reflects-≡ˡ a b (suc x) p q = inj-sm* {m = x} {l = a} {n = b} q

¬suc<0 : ∀ x → [ ¬ (suc x < 0) ]
¬suc<0 x (k , p) = snotz $ sym (+-suc k (suc x)) ∙ p

·-reflects-< : ∀ a b x → [ 0 < x ] → [ (a · x) < (b · x) ] → [ a < b ]
·-reflects-< zero zero x p q = q
·-reflects-< zero (suc b) x p q = 0<suc b
·-reflects-< (suc a) zero x p q = ⊥-elim {A = λ _ → [ suc a < 0 ]} $ ¬-<-zero q
·-reflects-< (suc a) (suc b) x p q = suc-creates-< a b .fst $ ·-reflects-< a b x p (+-createsˡ-< (a · x) (b · x) x .snd q)

min-comm : ∀ x y → min x y ≡ min y x
min-comm zero zero = refl
min-comm zero (suc y) = refl
min-comm (suc x) zero = refl
min-comm (suc x) (suc y) i = suc $ min-comm x y i

min-tightˡ : ∀ x y → [ x < y ] → min x y ≡ x
min-tightˡ zero zero x<y = refl
min-tightˡ zero (suc y) x<y = refl
min-tightˡ (suc x) zero x<y = ⊥-elim {A = λ _ → zero ≡ suc x} (¬suc<0 x x<y)
min-tightˡ (suc x) (suc y) x<y i = suc $ min-tightˡ x y (suc-creates-< x y .snd x<y) i

min-tightʳ : ∀ x y → [ y < x ] → min x y ≡ y
min-tightʳ x y y<x = min-comm x y ∙ min-tightˡ y x y<x

min-identity : ∀ x → min x x ≡ x
min-identity zero = refl
min-identity (suc x) i = suc $ min-identity x i

max-comm : ∀ x y → max x y ≡ max y x
max-comm zero zero = refl
max-comm zero (suc y) = refl
max-comm (suc x) zero = refl
max-comm (suc x) (suc y) i = suc $ max-comm x y i

max-tightˡ : ∀ x y → [ y < x ] → max x y ≡ x
max-tightˡ zero zero y<x = refl
max-tightˡ zero (suc y) y<x = ⊥-elim {A = λ _ → suc y ≡ zero} (¬suc<0 y y<x)
max-tightˡ (suc x) zero y<x = refl
max-tightˡ (suc x) (suc y) y<x i = suc $ max-tightˡ x y (suc-creates-< y x .snd y<x) i

max-tightʳ : ∀ x y → [ x < y ] → max x y ≡ y
max-tightʳ x y x<y = max-comm x y ∙ max-tightˡ y x x<y

max-identity : ∀ x → max x x ≡ x
max-identity zero = refl
max-identity (suc x) i = suc $ max-identity x i

-- +-reflects-< : ∀ a b x → [ a + x < b + x ] → [ a < b ]
-- +-reflects-< a b x

-- suc-preserves-min : ∀ x y → suc (min x y) ≡ min (suc x) (suc y)
-- suc-preserves-min zero y = refl
-- suc-preserves-min (suc x) zero = refl
-- suc-preserves-min (suc x) (suc y) = refl
--
-- min-dichotomy : ∀ x y → (min x y ≡ x) ⊎ (min x y ≡ y)
-- min-dichotomy zero y = inl refl
-- min-dichotomy (suc x) zero = inr refl
-- min-dichotomy (suc x) (suc y) with min-dichotomy x y
-- ... | inl p = inl λ i → suc (p i)
-- ... | inr p = inr λ i → suc (p i)

data MinTrichtotomy (x y : ℕ) : Type where
  min-lt : min x y ≡ x → [ x < y ]   → MinTrichtotomy x y
  min-gt : min x y ≡ y → [ y < x ]   → MinTrichtotomy x y
  min-eq : min x y ≡ x → min x y ≡ y → MinTrichtotomy x y

data MaxTrichtotomy (x y : ℕ) : Type where
  max-lt : max x y ≡ y → [ x < y ]   → MaxTrichtotomy x y
  max-gt : max x y ≡ x → [ y < x ]   → MaxTrichtotomy x y
  max-eq : max x y ≡ x → max x y ≡ y → MaxTrichtotomy x y

abstract
  min-trichotomy : ∀ x y → MinTrichtotomy x y
  min-trichotomy zero zero = min-eq refl refl
  min-trichotomy zero (suc y) = min-lt refl (y , (+-comm y 1))
  min-trichotomy (suc x) zero = min-gt refl (x , (+-comm x 1))
  min-trichotomy (suc x) (suc y) with min-trichotomy x y
  ... | min-lt p (k , q) = min-lt (λ i → suc (p i)) (k , (+-assoc k 1 (suc x) ∙ (λ i → +-comm k 1 i + suc x) ∙ (λ i → 1 + q i)))
  ... | min-gt p (k , q) = min-gt (λ i → suc (p i)) (k , (+-assoc k 1 (suc y) ∙ (λ i → +-comm k 1 i + suc y) ∙ (λ i → 1 + q i)))
  ... | min-eq p q       = min-eq (λ i → suc (p i)) (λ i → suc (q i))

  max-trichotomy : ∀ x y → MaxTrichtotomy x y
  max-trichotomy zero zero = max-eq refl refl
  max-trichotomy zero (suc y) = max-lt refl (y , (+-comm y 1))
  max-trichotomy (suc x) zero = max-gt refl (x , (+-comm x 1))
  max-trichotomy (suc x) (suc y) with max-trichotomy x y
  ... | max-lt p (k , q) = max-lt (λ i → suc (p i)) (k , (+-assoc k 1 (suc x) ∙ (λ i → +-comm k 1 i + suc x) ∙ (λ i → 1 + q i)))
  ... | max-gt p (k , q) = max-gt (λ i → suc (p i)) (k , (+-assoc k 1 (suc y) ∙ (λ i → +-comm k 1 i + suc y) ∙ (λ i → 1 + q i)))
  ... | max-eq p q       = max-eq (λ i → suc (p i)) (λ i → suc (q i))

  is-min : (x y z : ℕ) → [ ¬ᵖ (min x y < z) ⇔ ¬ᵖ (x < z) ⊓ ¬ᵖ (y < z) ]
  is-min x y z .fst z≤minxy with min-trichotomy x y
  ... | min-lt p x<y = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → p i < z) $ <-trans {x} {y} {z} x<y y<z)
  ... | min-gt p y<x = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) $ <-trans {y} {x} {z} y<x x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → p i < z) y<z)
  ... | min-eq p q   = (λ x<z → z≤minxy $ pathTo⇐ (λ i → p i < z) x<z)
                     , (λ y<z → z≤minxy $ pathTo⇐ (λ i → q i < z) y<z)
  is-min x y z .snd (z≤x , z≤y) minxy<z with min-trichotomy x y
  ... | min-lt p _   = z≤x $ pathTo⇒ (λ i → p i < z) minxy<z
  ... | min-gt p _   = z≤y $ pathTo⇒ (λ i → p i < z) minxy<z
  ... | min-eq p q   = z≤x $ pathTo⇒ (λ i → p i < z) minxy<z

  is-max : (x y z : ℕ) → [ ¬ᵖ (z < max x y) ⇔ ¬ᵖ (z < x) ⊓ ¬ᵖ (z < y) ]
  is-max x y z .fst maxxy≤z with max-trichotomy x y
  ... | max-gt p y<x = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<x )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < p i) $ <-trans {z} {y} {x} z<y y<x )
  ... | max-lt p x<y = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) $ <-trans {z} {x} {y} z<x x<y )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<y )
  ... | max-eq p q   = (λ z<x → maxxy≤z $ pathTo⇐ (λ i → z < p i) z<x )
                     , (λ z<y → maxxy≤z $ pathTo⇐ (λ i → z < q i) z<y )
  is-max x y z .snd (z≤x , z≤y) maxxy<z with max-trichotomy x y
  ... | max-gt p _   = z≤x $ pathTo⇒ (λ i → z < p i) maxxy<z
  ... | max-lt p _   = z≤y $ pathTo⇒ (λ i → z < p i) maxxy<z
  ... | max-eq p q   = z≤x $ pathTo⇒ (λ i → z < p i) maxxy<z

abstract
  -- NOTE: maybe some clever use of cotrans makes this a bit shorter
  +-<-ext : (w x y z : ℕ) → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
  +-<-ext w x y z (k , k+suc[w+x]≡y+z) with w ≟ y | x ≟ z
  ... | lt w<y | q = ∣ inl w<y ∣
  ... | gt (l , l+suc[y]≡w) | q = inrᵖ (k + suc l , inj-m+ ((
    y + ((k + suc l) + suc x) ≡⟨ +-assoc y (k + suc l) (suc x) ⟩
    (y + (k + suc l)) + suc x ≡⟨ (λ i → +-assoc y k (suc l) i + suc x) ⟩
    ((y + k) + suc l) + suc x ≡⟨ (λ i → (+-comm y k i + suc l) + suc x) ⟩
    ((k + y) + suc l) + suc x ≡⟨ (λ i → +-assoc k y (suc l) (~ i) + suc x) ⟩
    (k + (y + suc l)) + suc x ≡⟨ sym $ +-assoc k (y + suc l) (suc x) ⟩
    k + ((y + suc l) + suc x) ≡⟨ (λ i → k + (+-suc y l i + suc x)) ⟩
    k + (suc (y + l) + suc x) ≡⟨ (λ i → k + (suc (+-comm y l i) + suc x)) ⟩
    k + (suc (l + y) + suc x) ≡⟨ (λ i → k + (+-suc l y (~ i) + suc x)) ⟩
    k + ((l + suc y) + suc x) ≡⟨ (λ i → k + +-suc (l + suc y) x i) ⟩
    k + suc ((l + suc y) + x) ≡⟨ (λ i → k + suc (l+suc[y]≡w i + x)) ⟩
    k + suc (w + x) ∎) ∙ k+suc[w+x]≡y+z))
  ... | eq w≡y | q = inrᵖ (k , inj-m+ ((
    y + (k + suc x) ≡⟨ +-assoc y k (suc x) ⟩
    (y + k) + suc x ≡⟨ (λ i → +-comm y k i + suc x) ⟩
    (k + y) + suc x ≡⟨ sym $ +-assoc k y (suc x) ⟩
    k + (y + suc x) ≡⟨ (λ i → k + +-suc y x i) ⟩
    k + suc (y + x) ≡⟨ (λ i → k + suc (w≡y (~ i) + x)) ⟩
    k + suc (w + x) ∎) ∙ k+suc[w+x]≡y+z))

  -- NOTE: instead of equational reasoning, this might follow more easily from induction on `z`?
  ·-preserves-< : (x y z : ℕ) → [ 0 < z ] → [ x < y ] → [ (x · z) < (y · z) ]
  ·-preserves-< x y z (k , k+1≡z) (l , l+suc[x]≡y) = l · z + k , (
    (l · z + k) + suc (x · z) ≡⟨ sym $ +-assoc (l · z) k (suc (x · z)) ⟩
    l · z + (k + suc (x · z)) ≡⟨ refl ⟩ -- 1 + x ≡ suc x holds definitionally
    l · z + (k + (1 + x · z)) ≡⟨ (λ i → l · z + +-assoc k 1 (x · z) i) ⟩
    l · z + ((k + 1) + x · z) ≡⟨ (λ i → l · z + (k+1≡z i + x · z)) ⟩
    l · z + (z + x · z)       ≡⟨ refl ⟩ -- suc x · z ≡ z + x · z holds definitionally
    l · z + (suc x) · z       ≡⟨ ·-distribʳ l (suc x) z ⟩
    (l + suc x) · z           ∎) ∙ (λ i → l+suc[x]≡y i · z) ∙ refl

  -- ·-reflects-< : (x y z : ℕ) → [ 0 < z ] → [ (x · z) < (y · z) ] → [ x < y ]
  -- ·-reflects-< x y zero (k , k+1≡z) _ = ⊥-elim {A = λ _ → [ x < y ]} $ snotz (sym (+-comm k 1) ∙ k+1≡z)
  -- ·-reflects-< x y (suc zero) _ (l , l+suc[xz]≡yz) = l , (λ i → l + suc (·-identityʳ x (~ i))) ∙ l+suc[xz]≡yz ∙ ·-identityʳ y
  -- ·-reflects-< x y (suc (suc z)) _ p@(l , l+suc[xz]≡yz) =
  --   let ind = {! ·-reflects-< x y (suc z) (0<suc z)   !}
  --     -- (x · suc (suc z)) < (y · suc (suc z))
  --     -- x + x · suc z < y + y · suc z
  --     -- (x + x · suc z) + < (y + y · suc z)
  --   in {! ·-suc x (suc z)  !}
  -- -- ·-reflects-< x y zero 0<z xz<yz = {!   !} -- ·-suc x z
  -- -- ·-reflects-< x y (suc z) 0<z xz<yz = {! ·-reflects-< x y z  !}
  -- --   (x · suc z) < (y · suc z)

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℕ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _·_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℕ
·-Semigroup .IsSemigroup.is-assoc = ·-assoc

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-zero x , refl

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
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  a b c = <-trans {a} {b} {c}
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

bundle : LinearlyOrderedCommSemiring {ℓ-zero} {ℓ-zero}
bundle .LinearlyOrderedCommSemiring.Carrier                         = ℕ
bundle .LinearlyOrderedCommSemiring.0f                              = 0
bundle .LinearlyOrderedCommSemiring.1f                              = 1
bundle .LinearlyOrderedCommSemiring._+_                             = _+_
bundle .LinearlyOrderedCommSemiring._·_                             = _·_
bundle .LinearlyOrderedCommSemiring.min                             = min
bundle .LinearlyOrderedCommSemiring.max                             = max
bundle .LinearlyOrderedCommSemiring._<_                             = _<_
bundle .LinearlyOrderedCommSemiring.is-LinearlyOrderedCommSemiring  = is-LinearlyOrderedCommSemiring
