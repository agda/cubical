{-

This file proves a variety of basic results about paths:

- refl, sym, cong and composition of paths. This is used to set up
  equational reasoning.

- Transport, subst and functional extensionality

- J and its computation rule (up to a path)

- Σ-types and contractibility of singletons

- Converting PathP to and from a homogeneous path with transp

- Direct definitions of lower h-levels

- Export natural numbers

- Export universe lifting

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Prelude where

open import Cubical.Core.Primitives public

infixr 30 _∙_
infixr 30 _∙₂_
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infixr 2.5 _≡⟨_⟩≡⟨_⟩_
infixl 4 _≡$_ _≡$S_

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

refl : x ≡ x
refl {x = x} _ = x
{-# INLINE refl #-}

sym : x ≡ y → y ≡ x
sym p i = p (~ i)
{-# INLINE sym #-}

-- symP infers the type of its argument from the type of its output
symP : {A : I → Type ℓ} → {x : A i1} → {y : A i0} →
       (p : PathP (λ i → A (~ i)) x y) → PathP A y x
symP p j = p (~ j)

-- symP infers the type of its output from the type of its argument
symP-fromGoal : {A : I → Type ℓ} → {x : A i0} → {y : A i1} →
       (p : PathP A x y) → PathP (λ i → A (~ i)) y x
symP-fromGoal p j = p (~ j)

cong : (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)
{-# INLINE cong #-}

{- `S` stands for simply typed. Using `congS` instead of `cong`
   can help Agda to solve metavariables that may otherwise remain unsolved.
-}
congS : ∀ {B : Type ℓ} → (f : A → B) (p : x ≡ y) → f x ≡ f y
congS f p i = f (p i)
{-# INLINE congS #-}

congP : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  (f : (i : I) → (a : A i) → B i a) {x : A i0} {y : A i1}
  (p : PathP A x y) → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
congP f p i = f i (p i)
{-# INLINE congP #-}

cong₂ : {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong₂ f p q i = f (p i) (q i)
{-# INLINE cong₂ #-}

congP₂ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  {C : (i : I) (a : A i) → B i a → Type ℓ''}
  (f : (i : I) → (a : A i) → (b : B i a) → C i a b)
  {x : A i0} {y : A i1} {u : B i0 x} {v : B i1 y}
  (p : PathP A x y) (q : PathP (λ i → B i (p i)) u v)
  → PathP (λ i → C i (p i) (q i)) (f i0 x u) (f i1 y v)
congP₂ f p q i = f i (p i) (q i)
{-# INLINE congP₂ #-}

{- The most natural notion of homogenous path composition
    in a cubical setting is double composition:

       x ∙ ∙ ∙ > w
       ^         ^
   p⁻¹ |         | r        ^
       |         |        j |
       y — — — > z          ∙ — >
            q                 i

   `p ∙∙ q ∙∙ r` gives the line at the top,
   `doubleCompPath-filler p q r` gives the whole square
-}

doubleComp-faces : {x y z w : A } (p : x ≡ y) (r : z ≡ w)
                 → (i : I) (j : I) → Partial (i ∨ ~ i) A
doubleComp-faces p r i j (i = i0) = p (~ j)
doubleComp-faces p r i j (i = i1) = r j

_∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
(p ∙∙ q ∙∙ r) i =
  hcomp (doubleComp-faces p r i) (q i)

doubleCompPath-filler : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hfill (doubleComp-faces p r i) (inS (q i)) j

-- any two definitions of double composition are equal
compPath-unique : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                  → (α β : Σ[ s ∈ x ≡ w ] PathP (λ j → p (~ j) ≡ r j) q s)
                  → α ≡ β
compPath-unique p q r (α , α-filler) (β , β-filler) t
  = (λ i → cb i1 i) , (λ j i → cb j i)
  where cb : I → I → _
        cb j i = hfill (λ j → λ { (t = i0) → α-filler j i
                                ; (t = i1) → β-filler j i
                                ; (i = i0) → p (~ j)
                                ; (i = i1) → r j })
                       (inS (q i)) j

{- For single homogenous path composition, we take `p = refl`:

     x ∙ ∙ ∙ > z
     ‖         ^
     ‖         | r        ^
     ‖         |        j |
     x — — — > y          ∙ — >
          q                 i

   `q ∙ r` gives the line at the top,
   `compPath-filler q r` gives the whole square
-}

_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

compPath-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler p q = doubleCompPath-filler refl p q

-- We could have also defined single composition by taking `r = refl`:

_∙'_ : x ≡ y → y ≡ z → x ≡ z
p ∙' q = p ∙∙ q ∙∙ refl

compPath'-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙' q)
compPath'-filler p q = doubleCompPath-filler p q refl

-- It's easy to show that `p ∙ q` also has such a filler:
compPath-filler' : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙ q)
compPath-filler' {z = z} p q j i =
  hcomp (λ k → λ { (i = i0) → p (~ j)
                 ; (i = i1) → q k
                 ; (j = i0) → q (i ∧ k) })
        (p (i ∨ ~ j))
-- Note: We can omit a (j = i1) case here since when (j = i1), the whole expression is
--  definitionally equal to `p ∙ q`. (Notice that `p ∙ q` is also an hcomp.) Nevertheless,
--  we could have given `compPath-filler p q k i` as the (j = i1) case.

-- From this, we can show that these two notions of composition are the same
compPath≡compPath' : (p : x ≡ y) (q : y ≡ z) → p ∙ q ≡ p ∙' q
compPath≡compPath' p q j =
  compPath-unique p q refl (p ∙ q  , compPath-filler' p q)
                           (p ∙' q , compPath'-filler p q) j .fst

-- Double composition agrees with iterated single composition
doubleCompPath≡compPath : {x y z w : A}
    (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r
doubleCompPath≡compPath p q r i j =
  hcomp (λ k → λ { (i = i1) → compPath-filler' p (q ∙ r) k j
                 ; (j = i0) → p (~ k)
                 ; (j = i1) → r (i ∨ k)})
        (compPath-filler q r i j)

-- Heterogeneous path composition and its filler:

-- Composition in a family indexed by the interval
compPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
            → PathP A x y → PathP (λ i → B i) y z → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathP {A = A} {x = x} {B = B} p q i =
  comp (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (p i)

-- Composition in a family indexed by a type
compPathP' : {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
             (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ i → B ((p ∙ q) i)) x' z'
compPathP' {B = B} {x' = x'} {p = p} {q = q} P Q i =
  comp (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x'  ;
                  (i = i1) → Q j })
       (P i)

compPathP-filler : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : A i1 ≡ B_i1} {z : B i1}
  (p : PathP A x y) (q : PathP (λ i → B i) y z)
  → PathP (λ j → PathP (λ k → (compPath-filler (λ i → A i) B j k)) x (q j)) p (compPathP p q)
compPathP-filler {A = A} {x = x} {B = B} p q j i =
  fill (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (inS (p i)) j

compPathP'-filler : {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
  (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
  → PathP (λ j → PathP (λ i → B (compPath-filler p q j i)) x' (Q j)) P (compPathP' {B = B} P Q)
compPathP'-filler {B = B} {x' = x'} {p = p} {q = q} P Q j i =
  fill (λ j → B (compPath-filler p q j i))
       (λ j → λ { (i = i0) → x'  ;
                  (i = i1) → Q j })
       (inS (P i))
       j

-- Syntax for chains of equational reasoning

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

≡⟨⟩-syntax : (x : A) → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

≡⟨⟩⟨⟩-syntax : (x y : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
≡⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
infixr 3 ≡⟨⟩⟨⟩-syntax
syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

_≡⟨_⟩≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_ ≡⟨ x≡y ⟩≡⟨ y≡z ⟩ z≡w = x≡y ∙∙ y≡z ∙∙ z≡w

_∎ : (x : A) → x ≡ x
_ ∎ = refl

-- Transport and subst

-- transport is a special case of transp
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
                   → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

-- We want B to be explicit in subst
subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

subst2 : ∀ {ℓ' ℓ''} {B : Type ℓ'} {z w : B} (C : A → B → Type ℓ'')
        (p : x ≡ y) (q : z ≡ w) → C x z → C y w
subst2 B p q b = transport (λ i → B (p i) (q i)) b

substRefl : ∀ {B : A → Type ℓ} {x} → (px : B x) → subst B refl px ≡ px
substRefl px = transportRefl px

subst-filler : (B : A → Type ℓ') (p : x ≡ y) (b : B x)
  → PathP (λ i → B (p i)) b (subst B p b)
subst-filler B p = transport-filler (cong B p)

subst2-filler : {B : Type ℓ'} {z w : B} (C : A → B → Type ℓ'')
                (p : x ≡ y) (q : z ≡ w) (c : C x z)
              → PathP (λ i → C (p i) (q i)) c (subst2 C p q c)
subst2-filler C p q = transport-filler (cong₂ C p q)

-- Function extensionality

funExt : {B : A → I → Type ℓ'}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → ((x : A) → PathP (B x) (f x) (g x))
  → PathP (λ i → (x : A) → B x i) f g
funExt p i x = p x i

implicitFunExt : {B : A → I → Type ℓ'}
  {f : {x : A} → B x i0} {g : {x : A} → B x i1}
  → ({x : A} → PathP (B x) (f {x}) (g {x}))
  → PathP (λ i → {x : A} → B x i) f g
implicitFunExt p i {x} = p {x} i

-- the inverse to funExt (see Functions.FunExtEquiv), converting paths
-- between functions to homotopies; `funExt⁻` is called `happly` and
-- defined by path induction in the HoTT book (see function 2.9.2 in
-- section 2.9)
funExt⁻ : {B : A → I → Type ℓ'}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → PathP (λ i → (x : A) → B x i) f g
  → ((x : A) → PathP (B x) (f x) (g x))
funExt⁻ eq x i = eq i x

implicitFunExt⁻ : {B : A → I → Type ℓ'}
  {f : {x : A} → B x i0} {g : {x : A} → B x i1}
  → PathP (λ i → {x : A} → B x i) f g
  → ({x : A} → PathP (B x) (f {x}) (g {x}))
implicitFunExt⁻ eq {x} i = eq i {x}

_≡$_ = funExt⁻

{- `S` stands for simply typed. Using `funExtS⁻` instead of `funExt⁻`
   can help Agda to solve metavariables that may otherwise remain unsolved.
-}
funExtS⁻ : {B : I → Type ℓ'}
  {f : (x : A) → B i0} {g : (x : A) → B i1}
  → PathP (λ i → (x : A) → B i) f g
  → ((x : A) → PathP (λ i → B i) (f x) (g x))
funExtS⁻ eq x i = eq i x

_≡$S_ = funExtS⁻

-- J for paths and its computation rule

module _ (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where

  J : (p : x ≡ y) → P y p
  J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : J refl ≡ d
  JRefl = transportRefl d

  J-∙ : (p : x ≡ y) (q : y ≡ z)
    → J (p ∙ q) ≡ transport (λ i → P (q i) (λ j → compPath-filler p q i j)) (J p)
  J-∙ p q k =
    transp
      (λ i → P (q (i ∨ ~ k))
      (λ j → compPath-filler p q (i ∨ ~ k) j)) (~ k)
      (J (λ j → compPath-filler p q (~ k) j))

-- Multi-variable versions of J

module _ {b : B x}
  (P : (y : A) (p : x ≡ y) (z : B y) (q : PathP (λ i → B (p i)) b z) → Type ℓ'')
  (d : P _ refl _ refl) where

  JDep : {y : A} (p : x ≡ y) {z : B y} (q : PathP (λ i → B (p i)) b z) → P _ p _ q
  JDep _ q = transport (λ i → P _ _ _ (λ j → q (i ∧ j))) d

  JDepRefl : JDep refl refl ≡ d
  JDepRefl = transportRefl d

module _ {x : A}
  {P : (y : A) → x ≡ y → Type ℓ'} {d : (y : A) (p : x ≡ y) → P y p}
  (Q : (y : A) (p : x ≡ y) (z : P y p) → d y p ≡ z → Type ℓ'')
  (r : Q _ refl _ refl) where

  private
    ΠQ : (y : A) → x ≡ y → _
    ΠQ y p = ∀ z q → Q y p z q

  J2 : {y : A} (p : x ≡ y) {z : P y p} (q : d y p ≡ z) → Q _ p _ q
  J2 p = J ΠQ (λ _ → J (Q x refl) r) p _

  J2Refl : J2 refl refl ≡ r
  J2Refl = (λ i → JRefl ΠQ (λ _ → J (Q x refl) r) i _ refl) ∙ JRefl (Q x refl) _

-- A prefix operator version of J that is more suitable to be nested

module _ {P : ∀ y → x ≡ y → Type ℓ'} (d : P x refl) where

  J>_ : ∀ y → (p : x ≡ y) → P y p
  J>_ _ p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  infix 10 J>_

-- Converting to and from a PathP

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transport (λ i → A i) x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transport (λ i → A i) x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

-- Whiskering a dependent path by a path
-- Double whiskering
_◁_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
      → a₀ ≡ a₀' → PathP A a₀' a₁ → a₁ ≡ a₁'
      → PathP A a₀ a₁'
(p ◁ P ▷ q) i =
  hcomp (λ j → λ {(i = i0) → p (~ j) ; (i = i1) → q j}) (P i)

doubleWhiskFiller :
  ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ a₁' : A i1}
      → (p : a₀ ≡ a₀') (pq : PathP A a₀' a₁) (q : a₁ ≡ a₁')
      → PathP (λ i → PathP A (p (~ i)) (q i))
               pq
               (p ◁ pq ▷ q)
doubleWhiskFiller p pq q k i =
  hfill (λ j → λ {(i = i0) → p (~ j) ; (i = i1) → q j})
        (inS (pq i))
        k

_◁_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ : A i1}
  → a₀ ≡ a₀' → PathP A a₀' a₁ → PathP A a₀ a₁
(p ◁ q) = p ◁ q ▷ refl

_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁' : A i1}
  → PathP A a₀ a₁ → a₁ ≡ a₁' → PathP A a₀ a₁'
p ▷ q  = refl ◁ p ▷ q

-- Direct definitions of lower h-levels

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isGroupoid : Type ℓ → Type ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

is2Groupoid : Type ℓ → Type ℓ
is2Groupoid A = ∀ a b → isGroupoid (Path A a b)

-- Contractibility of singletons

singlP : (A : I → Type ℓ) (a : A i0) → Type _
singlP A a = Σ[ x ∈ A i1 ] PathP A a x

singl : (a : A) → Type _
singl {A = A} a = singlP (λ _ → A) a

isContrSingl : (a : A) → isContr (singl a)
isContrSingl a .fst = (a , refl)
isContrSingl a .snd p i .fst = p .snd i
isContrSingl a .snd p i .snd j = p .snd (i ∧ j)

isContrSinglP : (A : I → Type ℓ) (a : A i0) → isContr (singlP A a)
isContrSinglP A a .fst = _ , transport-filler (λ i → A i) a
isContrSinglP A a .snd (x , p) i =
  _ , λ j → fill A (λ j → λ {(i = i0) → transport-filler (λ i → A i) a j; (i = i1) → p j}) (inS a) j

-- Higher cube types

SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

Square :
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Type _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

Cube :
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type _
Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathP (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

-- Horizontal composition of squares (along their second dimension)
-- See Cubical.Foundations.Path for vertical composition

_∙₂_ :
  {a₀₀ a₀₁ a₀₂ : A} {a₀₋ : a₀₀ ≡ a₀₁} {b₀₋ : a₀₁ ≡ a₀₂}
  {a₁₀ a₁₁ a₁₂ : A} {a₁₋ : a₁₀ ≡ a₁₁} {b₁₋ : a₁₁ ≡ a₁₂}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₋₂ : a₀₂ ≡ a₁₂}
  (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square b₀₋ b₁₋ a₋₁ a₋₂)
  → Square (a₀₋ ∙ b₀₋) (a₁₋ ∙ b₁₋) a₋₀ a₋₂
_∙₂_ = congP₂ (λ _ → _∙_)

-- Alternative (equivalent) definitions of hlevel n that give fillers for n-cubes instead of n-globes

isSet' : Type ℓ → Type ℓ
isSet' A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

isSet→isSet' : isSet A → isSet' A
isSet→isSet' Aset _ _ _ _ = toPathP (Aset _ _ _ _)

isSet'→isSet : isSet' A → isSet A
isSet'→isSet Aset' x y p q = Aset' p q refl refl

isGroupoid' : Type ℓ → Type ℓ
isGroupoid' A =
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁

-- Essential properties of isProp and isContr

isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP B b0 b1
isProp→PathP hB b0 b1 = toPathP (hB _ _ _)

isPropIsContr : isProp (isContr A)
isPropIsContr (c0 , h0) (c1 , h1) j .fst = h0 c1 j
isPropIsContr (c0 , h0) (c1 , h1) j .snd y i =
   hcomp (λ k → λ { (i = i0) → h0 (h0 c1 j) k;
                    (i = i1) → h0 y k;
                    (j = i0) → h0 (h0 y i) k;
                    (j = i1) → h0 (h1 y i) k})
         c0

isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b = sym (p a) ∙ p b

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

isProp→isSet' : isProp A → isSet' A
isProp→isSet' h {a} p q r s i j =
  hcomp (λ k → λ { (i = i0) → h a (p j) k
                 ; (i = i1) → h a (q j) k
                 ; (j = i0) → h a (r i) k
                 ; (j = i1) → h a (s i) k}) a

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropSingl : {a : A} → isProp (singl a)
isPropSingl = isContr→isProp (isContrSingl _)

isPropSinglP : {A : I → Type ℓ} {a : A i0} → isProp (singlP A a)
isPropSinglP = isContr→isProp (isContrSinglP _ _)

-- Universe lifting

record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
  constructor lift
  field
    lower : A

open Lift public

liftExt : ∀ {A : Type ℓ} {a b : Lift {ℓ} {ℓ'} A} → (lower a ≡ lower b) → a ≡ b
liftExt x i = lift (x i)
