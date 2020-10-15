{-# OPTIONS --cubical --no-import-sorts --safe #-}

{-

This file defines

sucPred : ∀ (i : Int) → sucInt (predInt i) ≡ i
predSuc : ∀ (i : Int) → predInt (sucInt i) ≡ i

discreteInt : discrete Int
isSetInt : isSet Int

addition of Int is defined _+_ : Int → Int → Int

as well as its commutativity and associativity
+-comm : ∀ (m n : Int) → m + n ≡ n + m
+-assoc : ∀ (m n o : Int) → m + (n + o) ≡ (m + n) + o

An alternate definition of _+_ is defined via ua,
namely _+'_, which helps us to easily prove

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)

-}

module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; discreteℕ) renaming
  ( _·_ to _·ⁿ_
  ; _+_ to _+ⁿ_
  ; _⊓_ to _⊓ⁿ_
  ; _⊔_ to _⊔ⁿ_
  )
open import Cubical.Data.Nat.Order as ℕᵒ using () renaming ( _<_ to _<ⁿ_ )
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base
open import Cubical.Functions.Logic using (pathTo⇒; ⊔-comm)
open import Cubical.HITs.PropositionalTruncation as PropTrunc using (propTruncIsProp)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Reflection.Base using (_$_) -- TODO: add this to Foundation.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

abs : Int → ℕ
abs (pos n) = n
abs (negsuc n) = suc n

Sign : Type₀
Sign = Bool

pattern spos = Bool.false
pattern sneg = Bool.true

_·ˢ_ : Sign → Sign → Sign
_·ˢ_ = _⊕_

sgn : Int → Bool
sgn (pos    n) = spos
sgn (negsuc n) = sneg

signed : Sign → ℕ → Int
signed spos      x  = pos x
signed sneg  zero   = pos 0
signed sneg (suc x) = neg (suc x)

sgn-signed : ∀ s n → sgn (signed s (suc n)) ≡ s
sgn-signed spos n = refl
sgn-signed sneg n = refl

abs-signed : ∀ s n → abs (signed s n) ≡ n
abs-signed spos      n  = refl
abs-signed sneg  zero   = refl
abs-signed sneg (suc n) = refl

signed-inv : ∀ a → signed (sgn a) (abs a) ≡ a
signed-inv (pos    n) = refl
signed-inv (negsuc n) = refl

signed-zero : ∀ s → signed s 0 ≡ 0
signed-zero spos = refl
signed-zero sneg = refl

signed-reflects-sgn : ∀ s₁ s₂ n m → signed s₁ (suc n) ≡ signed s₂ (suc m) → s₁ ≡ s₂
signed-reflects-sgn s₁ s₂ n m p = sym (sgn-signed s₁ n) ∙ (λ i → sgn (p i)) ∙ sgn-signed s₂ m

signed-reflects-abs : ∀ s₁ s₂ n m → signed s₁ n ≡ signed s₂ m → n ≡ m
signed-reflects-abs s₁ s₂ n m p = sym (abs-signed s₁ n) ∙ (λ i → abs (p i)) ∙ abs-signed s₂ m

sign-abs-≡ : ∀ a b → sgn a ≡ sgn b → abs a ≡ abs b → a ≡ b
sign-abs-≡ a b p q = transport (λ i → signed-inv a i ≡ signed-inv b i) λ i → signed (p i) (q i)

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

predInt-inj : ∀ a b → predInt a ≡ predInt b → a ≡ b
predInt-inj a b p = sym (sucPred a) ∙ cong sucInt p ∙ sucPred b

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : Int → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : Int → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : Int → Type₀
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

discreteInt : Discrete Int
discreteInt (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteInt (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteInt (negsuc n) (pos m) = no (negsucNotpos n m)
discreteInt (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetInt : isSet Int
isSetInt = Discrete→isSet discreteInt

_ℕ-_ : ℕ → ℕ → Int
a ℕ- 0 = pos a
0 ℕ- suc b = negsuc b
suc a ℕ- suc b = a ℕ- b

_+pos_ : Int → ℕ  → Int
z +pos 0 = z
z +pos (suc n) = sucInt (z +pos n)

_+negsuc_ : Int → ℕ → Int
z +negsuc 0 = predInt z
z +negsuc (suc n) = predInt (z +negsuc n)

infix  8 -_
infixl 7 _·_ _⊓_
infixl 6 _+_ _-_ _⊔_
infix  4 _<_ -- _≤_

_+_ : Int → Int → Int
m + pos n = m +pos n
m + negsuc n = m +negsuc n

-- TODO: in `Cubical.Papers.RepresentationIndependence` we have
--   -_ : ℤ → ℤ
--   - x = 0 - x
-- there might be an advantage of defining -_ by _-_ and not the other way around
-- e.g. in Cubical.HITs.QuoInt we have
--   -_ : ℤ → ℤ
--   - signed s n = signed (not s) n
--   - posneg i   = posneg (~ i)

-_ : Int → Int
- pos  zero   = pos zero
- pos (suc n) = negsuc n
- negsuc   n  = pos (suc n)

_-_ : Int → Int → Int
m - n = m + (- n)

_·_ : Int → Int → Int
x · y  = signed (sgn x ⊕ sgn y) (abs x ·ⁿ abs y)

_<_ : ∀(x y : Int) → Type₀
pos    x < pos    y = x <ⁿ y
pos    x < negsuc y = ⊥
negsuc x < pos    y = ⊤
negsuc x < negsuc y = y <ⁿ x

_⊓_ : Int → Int → Int
(pos    x) ⊓ (pos    y) = pos (x ⊓ⁿ y)
(pos    x) ⊓ (negsuc y) = negsuc y
(negsuc x) ⊓ (pos    y) = negsuc x
(negsuc x) ⊓ (negsuc y) = negsuc (x ⊔ⁿ y)

_⊔_ : Int → Int → Int
(pos    x) ⊔ (pos    y) = pos (x ⊔ⁿ y)
(pos    x) ⊔ (negsuc y) = pos x
(negsuc x) ⊔ (pos    y) = pos y
(negsuc x) ⊔ (negsuc y) = negsuc (x ⊓ⁿ y)

neg-involutive : ∀ n → - - n ≡ n
neg-involutive (pos  zero  ) = refl
neg-involutive (pos (suc n)) = refl
neg-involutive (negsuc   n ) = refl

neg-signed-not : ∀ s n → - signed s n ≡ signed (not s) n
neg-signed-not spos  zero   = refl
neg-signed-not sneg  zero   = refl
neg-signed-not spos (suc n) = refl
neg-signed-not sneg (suc n) = refl

neg-abs : ∀ a → abs (- a) ≡ abs a
neg-abs (pos zero) = refl
neg-abs (pos (suc n)) = refl
neg-abs (negsuc n) = refl

neg-reflects-≡ : ∀ a b → - a ≡ - b → a ≡ b
neg-reflects-≡ a b p = sym (neg-involutive a) ∙ (λ i → - p i) ∙ neg-involutive b

abs-preserves-· : ∀ a b → abs (a · b) ≡ abs a ℕ.· abs b
abs-preserves-· a b = abs-signed (sgn a ⊕ sgn b) _

sucInt+pos : ∀ n m → sucInt (m +pos n) ≡ (sucInt m) +pos n
sucInt+pos zero m = refl
sucInt+pos (suc n) m = cong sucInt (sucInt+pos n m)

predInt+negsuc : ∀ n m → predInt (m +negsuc n) ≡ (predInt m) +negsuc n
predInt+negsuc zero m = refl
predInt+negsuc (suc n) m = cong predInt (predInt+negsuc n m)

sucInt+negsuc : ∀ n m → sucInt (m +negsuc n) ≡ (sucInt m) +negsuc n
sucInt+negsuc zero m = (sucPred _) ∙ (sym (predSuc _))
sucInt+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  m +negsuc n                    ≡[ i ]⟨ predSuc m (~ i) +negsuc n ⟩
  (predInt (sucInt m)) +negsuc n ≡⟨ sym (predInt+negsuc n (sucInt m)) ⟩
  predInt (sucInt m +negsuc n) ∎

predInt+pos : ∀ n m → predInt (m +pos n) ≡ (predInt m) +pos n
predInt+pos zero m = refl
predInt+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  m +pos n                    ≡[ i ]⟨ sucPred m (~ i) + pos n ⟩
  (sucInt (predInt m)) +pos n ≡⟨ sym (sucInt+pos n (predInt m))⟩
  (predInt m) +pos (suc n)    ∎

predInt+ : ∀ m n → predInt (m + n) ≡ (predInt m) + n
predInt+ m (pos n) = predInt+pos n m
predInt+ m (negsuc n) = predInt+negsuc n m

+predInt : ∀ m n → predInt (m + n) ≡ m + (predInt n)
+predInt m (pos zero) = refl
+predInt m (pos (suc n)) = (predSuc (m + pos n)) ∙ (cong (_+_ m) (sym (predSuc (pos n))))
+predInt m (negsuc n) = refl

sucInt+ : ∀ m n → sucInt (m + n) ≡ (sucInt m) + n
sucInt+ m (pos n) = sucInt+pos n m
sucInt+ m (negsuc n) = sucInt+negsuc n m

+sucInt : ∀ m n → sucInt (m + n) ≡  m + (sucInt n)
+sucInt m (pos n) = refl
+sucInt m (negsuc zero) = sucPred _
+sucInt m (negsuc (suc n)) = (sucPred (m +negsuc n)) ∙ (cong (_+_ m) (sym (sucPred (negsuc n))))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucInt (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = cong predInt (pos0+ (negsuc n))

negsuc0+ : ∀ z → predInt z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = (sym (sucPred (pos n))) ∙ (cong sucInt (negsuc0+ _))
negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = cong predInt (negsuc0+ (negsuc n))

ind-comm : {A : Type₀} (_∙_ : A → A → A) (f : ℕ → A) (g : A → A)
           (p : ∀ {n} → f (suc n) ≡ g (f n))
           (g∙ : ∀ a b → g (a ∙ b) ≡ g a ∙ b)
           (∙g : ∀ a b → g (a ∙ b) ≡ a ∙ g b)
           (base : ∀ z → z ∙ f 0 ≡ f 0 ∙ z)
         → ∀ z n → z ∙ f n ≡ f n ∙ z
ind-comm _∙_ f g p g∙ ∙g base z 0 = base z
ind-comm _∙_ f g p g∙ ∙g base z (suc n) =
  z ∙ f (suc n) ≡[ i ]⟨ z ∙ p {n} i ⟩
  z ∙ g (f n)   ≡⟨ sym ( ∙g z (f n)) ⟩
  g (z ∙ f n)   ≡⟨ cong g IH ⟩
  g (f n ∙ z)   ≡⟨ g∙ (f n) z ⟩
  g (f n) ∙ z   ≡[ i ]⟨ p {n} (~ i) ∙ z ⟩
  f (suc n) ∙ z ∎
  where
  IH = ind-comm _∙_ f g p g∙ ∙g base z n

ind-assoc : {A : Type₀} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → g (a · b) ≡ a · (g b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → (m · n) · (f 0) ≡ m · (n · (f 0)))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
ind-assoc _·_ f g p q base m n 0 = sym (base m n)
ind-assoc _·_ f g p q base m n (suc o) =
    m · (n · (f (suc o))) ≡[ i ]⟨ m · (n · q {o} i) ⟩
    m · (n · (g (f o)))   ≡[ i ]⟨ m · (p n (f o) (~ i)) ⟩
    m · (g (n · (f o)))   ≡⟨ sym (p m (n · (f o)))⟩
    g (m · (n · (f o)))   ≡⟨ cong g IH ⟩
    g ((m · n) · (f o))   ≡⟨ p (m · n) (f o) ⟩
    (m · n) · (g (f o))   ≡[ i ]⟨ (m · n) · q {o} (~ i) ⟩
    (m · n) · (f (suc o)) ∎
    where
    IH = ind-assoc _·_ f g p q base m n o

+-comm : ∀ m n → m + n ≡ n + m
+-comm m (pos n) = ind-comm _+_ pos sucInt refl sucInt+ +sucInt pos0+ m n
+-comm m (negsuc n) = ind-comm _+_ negsuc predInt refl predInt+ +predInt negsuc0+ m n

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc m n (pos o) = ind-assoc _+_ pos sucInt +sucInt refl (λ _ _ → refl) m n o
+-assoc m n (negsuc o) = ind-assoc _+_ negsuc predInt +predInt refl +predInt m n o

·-nullifiesʳ : ∀ x → x · 0 ≡ 0
·-nullifiesʳ (pos    n) i = signed spos (ℕ.·-nullifiesʳ n i)
·-nullifiesʳ (negsuc n) i = signed sneg (ℕ.·-nullifiesʳ n i)

·-nullifiesˡ : ∀ x → 0 · x ≡ 0
·-nullifiesˡ (pos    n) i = pos (ℕ.·-nullifiesˡ n i)
·-nullifiesˡ (negsuc n)   = refl

+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ x = refl

+-identityˡ : ∀ x → 0 + x ≡ x
+-identityˡ x = +-comm 0 x

·-identityʳ : ∀ x → x · 1 ≡ x
·-identityʳ x = cong₂ signed (⊕-comm (sgn x) spos) (ℕ.·-identityʳ (abs x)) ∙ signed-inv x

·-identityˡ : ∀ x → 1 · x ≡ x
·-identityˡ x = (λ i → signed (sgn x) (ℕ.+-comm (abs x) 0 i)) ∙ signed-inv x

-- predInt· : ∀ m n → predInt (m · n) ≡ (predInt m) · n
-- predInt· m (pos n) = {! predInt·pos n m !}
-- predInt· m (negsuc n) = {! predInt·negsuc n m !}
--
-- ·predInt : ∀ m n → predInt (m · n) ≡ m · (predInt n)
-- ·predInt m (pos zero) = {! refl !}
-- ·predInt m (pos (suc n)) = {! (predSuc (m · pos n)) ∙ (cong (_·_ m) (sym (predSuc (pos n)))) !}
-- ·predInt m (negsuc n) = {! refl !}
--
-- sucInt· : ∀ m n → n + m · n ≡ (sucInt m) · n
-- sucInt· m (pos n) = {! sucInt·pos n m !}
-- sucInt· m (negsuc n) = {! sucInt·negsuc n m !}
--
-- ·sucInt : ∀ m n → m + m · n ≡  m · (sucInt n)
-- ·sucInt m (pos n) = {! refl !}
-- ·sucInt m (negsuc zero) = {! sucPred _ !}
-- ·sucInt m (negsuc (suc n)) = {! (sucPred (m ·negsuc n)) ∙ (cong (_·_ m) (sym (sucPred (negsuc n)))) !}
--
-- pos0· : ∀ z → z · pos 0 ≡ pos 0 · z
-- pos0· (pos zero) = refl
-- pos0· (pos (suc n)) = pos0· (pos n)
-- pos0· (negsuc zero) = refl
-- pos0· (negsuc (suc n)) = pos0· (negsuc n)
--
-- negsuc0· : ∀ z → z · negsuc 0 ≡ negsuc 0 · z
-- negsuc0· (pos zero) = refl
-- negsuc0· (pos (suc n)) = cong negsuc $ ℕ.·-identityʳ n ∙ sym (ℕ.+-zero n)
-- negsuc0· (negsuc zero) = refl
-- negsuc0· (negsuc (suc n)) = cong (pos ∘ suc ∘ suc) (ℕ.·-identityʳ n ∙ sym (ℕ.+-zero n))

·-comm : ∀ m n → m · n ≡ n · m
·-comm (pos m) n = cong₂ signed (⊕-comm spos (sgn n)) (ℕ.·-comm m (abs n))
·-comm (negsuc m) n = cong₂ signed (⊕-comm sneg (sgn n)) (ℕ.·-comm (suc m) (abs n))

predInt-neg : ∀ a → predInt (- a) ≡ - (sucInt a)
predInt-neg (pos     zero  ) = refl
predInt-neg (pos    (suc n)) = refl
predInt-neg (negsuc  zero  ) = refl
predInt-neg (negsuc (suc n)) = refl

sucInt-neg : ∀ a → sucInt (- a) ≡ - (predInt a)
sucInt-neg (pos     zero        ) = refl
sucInt-neg (pos    (suc zero)   ) = refl
sucInt-neg (pos    (suc (suc n))) = refl
sucInt-neg (negsuc  zero        ) = refl
sucInt-neg (negsuc (suc n)      ) = refl

private
  lem : ∀ n → -(0 + n) ≡ 0 - n
  lem n i = +-identityˡ (- +-identityˡ n i) (~ i)

negate-+ : ∀ m n → - (m + n) ≡  (- m) + (- n)
negate-+ (pos zero) = lem
negate-+ (pos (suc m)) n = (λ i → - sucInt+ (pos m) n (~ i)) ∙ sym (predInt-neg (pos m + n)) ∙ (λ i → predInt (negate-+ (pos m) n i)) ∙ predInt+ (- pos m) (- n) ∙ λ i → predInt-neg (pos m) i + - n
negate-+ (negsuc zero) n = predInt-inj (- (negsuc zero + n)) (pos 1 + - n) $ predInt-neg (negsuc 0 + n) ∙ (λ i → - sucInt+ (negsuc 0) n i) ∙ lem n ∙ sym (predInt+ (pos 1) (- n))
negate-+ (negsuc (suc m)) n = (λ i → - predInt+ (negsuc m) n (~ i)) ∙ sym (sucInt-neg (negsuc m + n)) ∙ (λ i → sucInt (negate-+ (negsuc m) n i)) ∙ sucInt+ (pos (suc m)) (- n)

negate-·ˡ : ∀ a b → -(a · b) ≡ (- a) · b
negate-·ˡ (pos zero) b = neg-signed-not (sgn b) 0 ∙ signed-zero (not (sgn b)) ∙ sym (signed-zero (sgn b))
negate-·ˡ (pos (suc n)) b = neg-signed-not (sgn b) _
negate-·ˡ (negsuc n) b = neg-signed-not (not (sgn b)) _ ∙ cong₂ signed (notnot (sgn b)) refl

negate-·ʳ : ∀ a b → -(a · b) ≡ a · (- b)
negate-·ʳ a b = (λ i → - ·-comm a b i) ∙ negate-·ˡ b a ∙ ·-comm (- b) a

negsuc+negsuc : ∀ a x → (negsuc a +negsuc x) ≡ negsuc (suc (a +ⁿ x))
negsuc+negsuc a zero = λ i → negsuc $ suc $ ℕ.+-comm 0 a i
negsuc+negsuc a (suc x) = let r = negsuc+negsuc a x in
  predInt (negsuc a +negsuc x)    ≡⟨ (λ i → predInt (r i)) ⟩
  predInt (negsuc (suc (a +ⁿ x))) ≡⟨ refl ⟩
  negsuc (suc (suc (a +ⁿ x)))     ≡⟨ (λ i → negsuc $ suc $ ℕ.+-suc a x (~ i)) ⟩
  negsuc (suc (a +ⁿ suc x))       ∎

signed-distrib : ∀ s m n → signed s (m +ⁿ n) ≡ signed s m + signed s n
signed-distrib s zero n = (sym $ +-identityˡ (signed s n)) ∙ λ i → signed-zero s (~ i) + signed s n
signed-distrib spos (suc m) n = cong sucInt (signed-distrib spos m n) ∙ sucInt+pos n (pos m)
signed-distrib sneg (suc m) zero i = negsuc (ℕ.+-comm m 0 i)
signed-distrib sneg (suc m) (suc n) = (λ i → negsuc (ℕ.+-suc m n i)) ∙  sym (negsuc+negsuc m n)

·-pos-suc : ∀ m n → pos (suc m) · n ≡ n + pos m · n
·-pos-suc m n = signed-distrib (sgn n) (abs n) (m ℕ.· abs n) ∙ λ i → signed-inv n i + signed (sgn n) (m ·ⁿ abs n)

-- ·-sucIntˡ : ∀ m n → (sucInt m · n) ≡ (n + (m · n))
-- -- ·-sucIntˡ m n = ·-comm (sucInt m) n ∙ {!   !} ∙ λ i → n + ·-comm n m i
-- ·-sucIntˡ m (pos n) = {!   !}
-- ·-sucIntˡ m (negsuc n) = {!   !}

-- private
--   lem : ∀ s₁ s₂ n → signed s₁ n ≡ signed s₂ n →

-- this is a similar proof to the one in Cubical.HITs.QuoInt.Properties
--   but we have less definitional equalities
-- ·-assoc : ∀ m n o → m · (n · o) ≡ m · n · o
-- ·-assoc m n o     with abs m | signed-inv m
-- ... | zero   | pm = {!   !}
-- ... | suc mⁿ | pm with abs n | signed-inv n
-- ... | zero   | pn = (λ i → signed s₁ (γ₁ i)) ∙ signed-zero s₁ ∙ sym (signed-zero s₂) ∙ (λ i → signed s₂ (γ₂ i)) where
--   s₁ = sgn m ⊕ sgn (signed (sgn n ⊕ sgn o) 0)
--   s₂ = sgn (signed (sgn m ⊕ sgn n) (mⁿ ·ⁿ 0)) ⊕ sgn o
--   γ₁ = suc mⁿ ·ⁿ abs (signed (sgn n ⊕ sgn o) 0)        ≡⟨ {!   !} ⟩
--        suc mⁿ ·ⁿ 0                                     ≡⟨ {!   !} ⟩
--        0                                               ∎
--   γ₂ = 0                                               ≡⟨ {!   !} ⟩
--        0 ·ⁿ abs o                                      ≡⟨ {!   !} ⟩
--        (mⁿ ·ⁿ 0) ·ⁿ abs o                              ≡⟨ {!   !} ⟩
--        abs (signed (sgn m ⊕ sgn n) (mⁿ ·ⁿ 0)) ·ⁿ abs o ∎
-- ... | suc nⁿ | pn with abs o | signed-inv o
-- ... | zero   | po = (λ i → signed s₁ (γ₁ i)) ∙ signed-zero s₁ ∙ sym (signed-zero s₂) ∙ (λ i → signed s₂ (γ₂ i)) where
--   s₁ = sgn m ⊕ sgn (signed (sgn n ⊕ sgn o) (nⁿ ·ⁿ zero))
--   s₂ = sgn (signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ)) ⊕ sgn o
--   γ₁ = suc mⁿ ·ⁿ abs (signed (sgn n ⊕ sgn o) (nⁿ ·ⁿ 0)) ≡[ i ]⟨ suc mⁿ ·ⁿ abs-signed (sgn n ⊕ sgn o) (nⁿ ·ⁿ 0) i ⟩
--        suc mⁿ ·ⁿ                             (nⁿ ·ⁿ 0)  ≡[ i ]⟨ suc mⁿ ·ⁿ (ℕ.·-nullifiesʳ nⁿ i) ⟩
--        suc mⁿ ·ⁿ                                    0   ≡⟨ ℕ.·-nullifiesʳ (suc mⁿ) ⟩
--                                                     0 ∎
--   γ₂ = 0 ≡⟨ sym $ ℕ.·-nullifiesʳ (abs (signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ))) ⟩
--        abs (signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ)) ·ⁿ 0 ∎
-- ... | suc oⁿ | po = cong₂ signed γ₁ γ₂ where
--   γ₁ = sgn m ⊕ sgn (signed (sgn n ⊕ sgn o) (suc nⁿ ·ⁿ suc oⁿ)) ≡[ i ]⟨ sgn m ⊕ sgn-signed (sgn n ⊕ sgn o) (oⁿ +ⁿ nⁿ ·ⁿ suc oⁿ) i ⟩
--        sgn m ⊕ (sgn n ⊕ sgn o)                                 ≡⟨ ⊕-assoc (sgn m) (sgn n) (sgn o) ⟩
--        (sgn m ⊕ sgn n) ⊕ sgn o                                 ≡[ i ]⟨ sgn-signed (sgn m ⊕ sgn n) (nⁿ +ⁿ mⁿ ·ⁿ suc nⁿ) (~ i) ⊕ sgn o ⟩
--        sgn (signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ)) ⊕ sgn o ∎
--   γ₂ = suc mⁿ ·ⁿ abs (signed (sgn n ⊕ sgn o) (suc nⁿ ·ⁿ suc oⁿ)) ≡[ i ]⟨ suc mⁿ ·ⁿ abs-signed (sgn n ⊕ sgn o) (suc nⁿ ·ⁿ suc oⁿ) i ⟩
--        suc mⁿ ·ⁿ (suc nⁿ ·ⁿ suc oⁿ)                              ≡⟨ ℕ.·-assoc (suc mⁿ) (suc nⁿ) (suc oⁿ) ⟩
--        (suc mⁿ ·ⁿ suc nⁿ) ·ⁿ suc oⁿ                              ≡[ i ]⟨ abs-signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ) (~ i) ·ⁿ suc oⁿ ⟩
--        abs (signed (sgn m ⊕ sgn n) (suc mⁿ ·ⁿ suc nⁿ)) ·ⁿ suc oⁿ ∎


private
  lemma2 : ∀ a b c →  c +ⁿ (b +ⁿ a ·ⁿ suc b) ·ⁿ suc c
                   ≡ (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ suc (c +ⁿ b ·ⁿ suc c)
  lemma2 a b c =
    c +ⁿ (b +ⁿ a ·ⁿ suc b) ·ⁿ suc c                 ≡⟨ (λ i → c +ⁿ ℕ.·-distribʳ b (a ·ⁿ suc b) (suc c) (~ i)) ⟩
    c +ⁿ (b ·ⁿ suc c +ⁿ (a ·ⁿ suc b) ·ⁿ suc c)      ≡⟨ ℕ.+-assoc c _ _ ⟩
    (c +ⁿ b ·ⁿ suc c) +ⁿ (a ·ⁿ suc b) ·ⁿ suc c      ≡⟨ (λ i → (c +ⁿ b ·ⁿ suc c) +ⁿ ℕ.·-assoc a (suc b) (suc c) (~ i)) ⟩
    (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ (suc b ·ⁿ suc c)      ≡⟨ refl ⟩
    (c +ⁿ b ·ⁿ suc c) +ⁿ a ·ⁿ suc (c +ⁿ b ·ⁿ suc c) ∎

-- this is a proof ported from the non-cubical standard library
·-assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
·-assoc (pos 0) y z = (λ i → ·-nullifiesˡ y i · z) ∙ ·-nullifiesˡ z ∙ sym (·-nullifiesˡ (y · z))
·-assoc x (pos 0) z = (λ i → ·-nullifiesʳ x i · z) ∙ ·-nullifiesˡ z ∙ sym (·-nullifiesʳ x)  ∙ (λ i → x · ·-nullifiesˡ z (~ i))
·-assoc x y (pos 0) = ·-nullifiesʳ (x · y) ∙ sym (·-nullifiesʳ x) ∙ (λ i → x · ·-nullifiesʳ y (~ i))
·-assoc (negsuc   a ) (negsuc   b ) (pos (suc c)) i = (pos (suc (lemma2 a b c i)))
·-assoc (negsuc   a ) (pos (suc b)) (negsuc   c ) i = (pos (suc (lemma2 a b c i)))
·-assoc (pos (suc a)) (pos (suc b)) (pos (suc c)) i = (pos (suc (lemma2 a b c i)))
·-assoc (pos (suc a)) (negsuc   b ) (negsuc   c ) i = (pos (suc (lemma2 a b c i)))
·-assoc (negsuc   a ) (negsuc   b ) (negsuc   c ) i = (negsuc   (lemma2 a b c i) )
·-assoc (negsuc   a ) (pos (suc b)) (pos (suc c)) i = (negsuc   (lemma2 a b c i) )
·-assoc (pos (suc a)) (negsuc   b ) (pos (suc c)) i = (negsuc   (lemma2 a b c i) )
·-assoc (pos (suc a)) (pos (suc b)) (negsuc   c ) i = (negsuc   (lemma2 a b c i) )

-- this is a similar proof to the one in Cubical.HITs.QuoInt.Properties
·-distribˡ-pos : ∀ o m n → (pos o · m) + (pos o · n) ≡ pos o · (m + n)
·-distribˡ-pos zero m n = (λ i → ·-nullifiesˡ m i + ·-nullifiesˡ n i) ∙ sym (·-nullifiesˡ (m + n))
·-distribˡ-pos (suc o) m n =
  pos (suc o) · m + pos (suc o) · n ≡[ i ]⟨ ·-pos-suc o m i + ·-pos-suc o n i ⟩
  m + pos o · m + (n + pos o · n)   ≡⟨ +-assoc (m + pos o · m) n (pos o · n) ⟩
  m + pos o · m + n + pos o · n     ≡[ i ]⟨ +-assoc m (pos o · m) n (~ i) + pos o · n ⟩
  m + (pos o · m + n) + pos o · n   ≡[ i ]⟨ m + +-comm (pos o · m) n i + pos o · n ⟩
  m + (n + pos o · m) + pos o · n   ≡[ i ]⟨ +-assoc m n (pos o · m) i + pos o · n ⟩
  m + n + pos o · m + pos o · n     ≡⟨ sym (+-assoc (m + n) (pos o · m) (pos o · n)) ⟩
  m + n + (pos o · m + pos o · n)   ≡⟨ cong ((m + n) +_) (·-distribˡ-pos o m n) ⟩
  m + n + pos o · (m + n)           ≡⟨ sym (·-pos-suc o (m + n)) ⟩
  pos (suc o) · (m + n) ∎

neg-pos-neg : ∀ x → - pos x ≡ neg x
neg-pos-neg zero = refl
neg-pos-neg (suc x) = refl

·-distribˡ-neg : ∀ o m n → (neg o · m) + (neg o · n) ≡ neg o · (m + n)
·-distribˡ-neg o m n =
     neg o · m  +    neg o · n  ≡[ i ]⟨ neg-pos-neg o (~ i) · m + neg-pos-neg o (~ i) · n ⟩
  -  pos o · m  + -  pos o · n  ≡[ i ]⟨ negate-·ˡ (pos o) m (~ i) + negate-·ˡ (pos o) n (~ i) ⟩
  - (pos o · m) + - (pos o · n) ≡⟨ sym (negate-+ (pos o · m) (pos o · n)) ⟩
  - (pos o · m + pos o · n)     ≡⟨ cong -_ (·-distribˡ-pos o m n) ⟩
  - (pos o · (m + n))           ≡⟨ negate-·ˡ (pos o) (m + n) ⟩
  -  pos o · (m + n)            ≡[ i ]⟨ neg-pos-neg o i · (m + n) ⟩
     neg o · (m + n)            ∎

·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
·-distribˡ (pos    o) m n = ·-distribˡ-pos o m n
·-distribˡ (negsuc o) m n = ·-distribˡ-neg (suc o) m n

·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
·-distribʳ m n o = (λ i → ·-comm m o i + ·-comm n o i) ∙ ·-distribˡ o m n ∙ ·-comm o (m + n)

private
  possuc+negsuc≡0 : ∀ n → (pos (suc n) +negsuc n) ≡ pos 0
  possuc+negsuc≡0 zero = refl
  possuc+negsuc≡0 (suc n) = sym ind ∙ possuc+negsuc≡0 n where
    ind =           pos      (suc n)   +negsuc n  ≡⟨ refl ⟩
           predInt (pos (suc (suc n))) +negsuc n  ≡⟨ sym $ predInt+negsuc n (pos (suc (suc n))) ⟩
           predInt (pos (suc (suc n))  +negsuc n) ∎

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

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.
-- Use this to define _+'_ for which is easier to prove
-- isEquiv (λ n → n +' m) since _+'_ is defined by transport

sucPathInt : Int ≡ Int
sucPathInt = ua (sucInt , isoToIsEquiv (iso sucInt predInt sucPred predSuc))

addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathInt

predPathInt : Int ≡ Int
predPathInt = ua (predInt , isoToIsEquiv (iso predInt sucInt predSuc sucPred))

subEq : ℕ → Int ≡ Int
subEq zero = refl
subEq (suc n) = (subEq n) ∙ predPathInt

_+'_ : Int → Int → Int
m +' pos n    = transport (addEq n) m
m +' negsuc n = transport (subEq (suc n)) m

+'≡+ : _+'_ ≡ _+_
+'≡+ i m (pos zero) = m
+'≡+ i m (pos (suc n)) = sucInt (+'≡+ i m (pos n))
+'≡+ i m (negsuc zero) = predInt m
+'≡+ i m (negsuc (suc n)) = predInt (+'≡+ i m (negsuc n)) --
  -- compPath (λ i → (+'≡+ i (predInt m) (negsuc n))) (sym (predInt+negsuc n m)) i

isEquivAddInt' : (m : Int) → isEquiv (λ n → n +' m)
isEquivAddInt' (pos n)    = isEquivTransport (addEq n)
isEquivAddInt' (negsuc n) = isEquivTransport (subEq (suc n))

isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt = subst (λ add → (m : Int) → isEquiv (λ n → add n m)) +'≡+ isEquivAddInt'

-- below is an alternate proof of isEquivAddInt for comparison
-- We also have two useful lemma here.

minusPlus : ∀ m n → (n - m) + m ≡ n
minusPlus (pos zero) n = refl
minusPlus (pos 1) = sucPred
minusPlus (pos (suc (suc m))) n =
  sucInt ((n +negsuc (suc m)) +pos (suc m)) ≡⟨ sucInt+pos (suc m) _ ⟩
  sucInt (n +negsuc (suc m)) +pos (suc m)   ≡[ i ]⟨ sucPred (n +negsuc m) i +pos (suc m) ⟩
  (n - pos (suc m)) +pos (suc m)            ≡⟨ minusPlus (pos (suc m)) n ⟩
  n ∎
minusPlus (negsuc zero) = predSuc
minusPlus (negsuc (suc m)) n =
  predInt (sucInt (sucInt (n +pos m)) +negsuc m) ≡⟨ predInt+negsuc m _ ⟩
  predInt (sucInt (sucInt (n +pos m))) +negsuc m ≡[ i ]⟨ predSuc (sucInt (n +pos m)) i +negsuc m ⟩
  sucInt (n +pos m) +negsuc m                    ≡⟨ minusPlus (negsuc m) n ⟩
  n ∎

plusMinus : ∀ m n → (n + m) - m ≡ n
plusMinus (pos zero) n = refl
plusMinus (pos (suc m)) = minusPlus (negsuc m)
plusMinus (negsuc m) = minusPlus (pos (suc m))

private
  alternateProof : (m : Int) → isEquiv (λ n → n + m)
  alternateProof m = isoToIsEquiv (iso (λ n → n + m)
                                       (λ n → n - m)
                                       (minusPlus m)
                                       (plusMinus m))

<-irrefl : ∀ a → ¬ (a < a)
<-irrefl (pos  zero  ) = ℕᵒ.<-irrefl 0
<-irrefl (pos (suc n)) = ℕᵒ.<-irrefl (suc n)
<-irrefl (negsuc   n ) = ℕᵒ.<-irrefl n

<-trans : ∀ a b c → a < b → b < c → a < c
<-trans (pos    a) (pos    b) (pos    c) a<b b<c = ℕᵒ.<-trans a<b b<c
<-trans (negsuc a) (pos    b) (pos    c) a<b b<c = tt
<-trans (negsuc a) (negsuc b) (pos    c) a<b b<c = tt
<-trans (negsuc a) (negsuc b) (negsuc c) a<b b<c = ℕᵒ.<-trans b<c a<b

<-asym : ∀ a b → a < b → ¬(b < a)
<-asym a b p q = <-irrefl _ (<-trans _ _ _ p q)

private
  swap-∥⊎∥ : ∀{ℓ ℓ'} (a : Type ℓ) (b : Type ℓ') → ∥ a ⊎ b ∥ → ∥ b ⊎ a ∥
  swap-∥⊎∥ a b = PropTrunc.elim (λ _ → propTruncIsProp) λ{ (inl p) → ∣ inr p ∣ ; (inr p) → ∣ inl p ∣ }

<-cotrans : ∀ a b x → a < b → ∥ (a < x) ⊎ (x < b) ∥
<-cotrans (pos    a) (pos    b) (pos    x) a<b = ℕᵒ.<-cotrans _ _ x a<b
<-cotrans (pos    a) (pos    b) (negsuc x) a<b = ∣ inr tt ∣
<-cotrans (negsuc a) (pos    b) (pos    x) a<b = ∣ inl tt ∣
<-cotrans (negsuc a) (pos    b) (negsuc x) a<b = ∣ inr tt ∣
<-cotrans (negsuc a) (negsuc b) (pos    x) a<b = ∣ inl tt ∣
<-cotrans (negsuc a) (negsuc b) (negsuc x) a<b = swap-∥⊎∥ _ _ (ℕᵒ.<-cotrans _ _ x a<b)

data Trichotomy (m n : Int) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

_≟_ : ∀ m n → Trichotomy m n
pos    a ≟ pos    b with a ℕᵒ.≟ b
... | ℕᵒ.lt p = lt p
... | ℕᵒ.eq p = eq λ i → pos (p i)
... | ℕᵒ.gt p = gt p
pos    a ≟ negsuc b = gt tt
negsuc a ≟ pos    b = lt tt
negsuc a ≟ negsuc b with a ℕᵒ.≟ b
... | ℕᵒ.lt p = gt p
... | ℕᵒ.eq p = eq λ i → negsuc (p i)
... | ℕᵒ.gt p = lt p

sucInt-reflects-< : ∀ x y → sucInt x < sucInt y → x < y
sucInt-reflects-< (pos         x ) (pos         y ) p = ℕᵒ.suc-reflects-< x y p
sucInt-reflects-< (pos         x ) (negsuc  zero  ) p = ℕᵒ.¬-<-zero p
sucInt-reflects-< (negsuc      x ) (pos         y ) p = tt
sucInt-reflects-< (negsuc  zero  ) (negsuc  zero  ) p = p
sucInt-reflects-< (negsuc (suc x)) (negsuc  zero  ) p = ℕᵒ.zero-<-suc x
sucInt-reflects-< (negsuc (suc x)) (negsuc (suc y)) p = ℕᵒ.suc-preserves-< y x p

predInt-reflects-< : ∀ x y → predInt x < predInt y → x < y
predInt-reflects-< (pos  zero  ) (pos  zero  ) p = p
predInt-reflects-< (pos  zero  ) (pos (suc y)) p = ℕᵒ.zero-<-suc y
predInt-reflects-< (pos (suc x)) (pos (suc y)) p = ℕᵒ.suc-preserves-< x y p
predInt-reflects-< (pos  zero  ) (negsuc   y ) p = ℕᵒ.¬-<-zero p
predInt-reflects-< (negsuc   x ) (pos      y ) p = tt
predInt-reflects-< (negsuc   x ) (negsuc   y ) p = ℕᵒ.suc-reflects-< y x p

sucInt-preserves-< : ∀ x y → x < y → sucInt x < sucInt y
sucInt-preserves-< (pos         x ) (pos         y ) p = ℕᵒ.suc-preserves-< x y p
sucInt-preserves-< (negsuc  zero  ) (pos         y ) p = ℕᵒ.zero-<-suc y
sucInt-preserves-< (negsuc (suc x)) (pos         y ) p = tt
sucInt-preserves-< (negsuc  zero  ) (negsuc  zero  ) p = p
sucInt-preserves-< (negsuc  zero  ) (negsuc (suc y)) p = ℕᵒ.¬-<-zero p
sucInt-preserves-< (negsuc (suc x)) (negsuc  zero  ) p = tt
sucInt-preserves-< (negsuc (suc x)) (negsuc (suc y)) p = ℕᵒ.suc-reflects-< y x p

predInt-preserves-< : ∀ x y → x < y → predInt x < predInt y
predInt-preserves-< (pos  zero  ) (pos  zero  ) p = p
predInt-preserves-< (pos  zero  ) (pos (suc y)) p = tt
predInt-preserves-< (pos (suc x)) (pos  zero  ) p = ℕᵒ.¬-<-zero p
predInt-preserves-< (pos (suc x)) (pos (suc y)) p = ℕᵒ.suc-reflects-< x y p
predInt-preserves-< (negsuc   x ) (pos  zero  ) p = ℕᵒ.zero-<-suc x
predInt-preserves-< (negsuc   x ) (pos (suc y)) p = tt
predInt-preserves-< (negsuc   x ) (negsuc   y ) p = ℕᵒ.suc-preserves-< y x p

+-preserves-<ʳ : ∀ a b x → a < b → (a + x) < (b + x)
+-preserves-<ʳ a b (pos     zero  ) a<b = a<b
+-preserves-<ʳ a b (pos    (suc n)) a<b =  sucInt-preserves-< (a +pos n) (b +pos n) (+-preserves-<ʳ a b (pos n) a<b)
+-preserves-<ʳ a b (negsuc  zero  ) a<b = predInt-preserves-< a b a<b
+-preserves-<ʳ a b (negsuc (suc n)) a<b = predInt-preserves-< (a +negsuc n) (b +negsuc n) (+-preserves-<ʳ a b (negsuc n) a<b)

+-reflects-<ʳ : ∀ a b x → (a + x) < (b + x) → a < b
+-reflects-<ʳ a b x =
  a +  x      < b +  x      →⟨ +-preserves-<ʳ (a + x) (b + x) (- x) ⟩
  a +  x - x  < b +  x - x  →⟨ transp (λ i → +-assoc a x (- x) (~ i) < +-assoc b x (- x) (~ i)) i0 ⟩
  a + (x - x) < b + (x - x) →⟨ transp (λ i → (a + +-inverseʳ x i) < (b + +-inverseʳ x i)) i0 ⟩
  a +  0      < b +  0      →⟨⟩
  a           < b           ◼

+-reflects-<ˡ : ∀ a b x → (x + a) < (x + b) → a < b
+-reflects-<ˡ a b x p = +-reflects-<ʳ a b x (transport (λ i → +-comm x a i < +-comm x b i) p)

+-<-extensional : ∀ w x y z → (w + x) < (y + z) → ∥ (w < y) ⊎ (x < z) ∥
+-<-extensional w x y z r with w ≟ y | x ≟ z
... | lt w<y | q = ∣ inl w<y ∣
... | eq w≡y | q = ∣ inr $ +-reflects-<ˡ x z y (transport (λ i → (w≡y i + x) < (y + z)) r) ∣
... | gt y<w | q = PropTrunc.elim (λ _ → propTruncIsProp) γ (<-cotrans (w + x) (y + z) (y + x) r)
  where γ : _ ⊎ _ → _
        γ (inl p) = ∣ inr (⊥.elim {A = λ _ → x < z} (<-asym y w y<w (+-reflects-<ʳ w y x p))) ∣
        γ (inr p) = ∣ inr (+-reflects-<ˡ x z y p) ∣
