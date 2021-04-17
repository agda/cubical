{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cubical.Epit.Ex2 where

open import Cubical.Epit.Part2
open import Cubical.Epit.Part3 hiding (Bool ; notPath)
open import Cubical.Epit.Ex1 hiding (B)



-- Exercises about Part 2:

-- Exercise 1 (easy): prove that the computation rule for J on refl
-- holds up to a path.
-- (hint: normalize the goal using C-u C-u C-c C-,)
JEq : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
      (d : P x refl) → J P d refl ≡ d
JEq {A = A} {x = x} P p i = transp (λ _ → P x refl) i p


-- Exercise 2 (easy): prove that isContr implies isProp
isContr→isProp : isContr A → isProp A
isContr→isProp (fst₁ , p) a b = sym (p a) ∙ p b


-- Exercise 3 (easy): prove that isProp implies isProp'
-- (hint: use isProp→isSet from the Part2)
isProp→isProp' : isProp A → isProp' A
fst (isProp→isProp' p x y) = p x y
snd (isProp→isProp' p x y) q = isProp→isSet p _ _ _ _


-- Exercise 4 (easy): prove the following lemma
-- (hint: use the solutions to exercises 2 and 3)
isContr→isContr≡ : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContr≡ c = isProp→isProp' (isContr→isProp c)


-- Exercise 5: use transp to turn a PathP into a transport
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
          → PathP A x y
          → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)


-- The converse is harder to prove so we give it:
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
        → transport (λ i → A i) x ≡ y
        → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → p j })
        (transp (λ j → A (i ∧ j)) (~ i) x)


-- Exercise 6: prove that two Σ-types where the second component is a
-- proposition is equal if the first projections are equal.
-- (hint: use ΣPathP and toPathP)
Σ≡Prop : {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : fst u ≡ fst v) → u ≡ v
Σ≡Prop {B = B} {u = u} {v = v} h p = ΣPathP (p , (toPathP (h _ _ _)))


-- Exercice 7 (harder): prove that being contractible is a proposition.
-- (hint: the second component can be given by a suitable higher
-- dimensional hcomp)
isPropIsContr : isProp (isContr A)
fst (isPropIsContr (c1 , p1) (c2 , p2) j) = (p1 c2) j
snd (isPropIsContr (c1 , p1) (c2 , p2) j) x i =
  hcomp (λ k → λ {(i = i0) → {!!}
                 ; (i = i1) → {!!}
                 ; (j = i0) → {!!}
                 ; (j = i1) → {!!}})
        {!!}
{-
j = i0 ⊢ p1 x i
j = i1 ⊢ p2 x i
i = i0 ⊢ p1 c2 j
i = i1 ⊢ x
-}
{-
  hcomp (λ k → λ {(i = i1) → {!p1 (p1 x (~ k))!}
                 ; (i = i0) → {!!}
                 ; (j = i0) → {!!}
                 ; (j = i1) → {!!}})
        {!!}
-}
{-
  hcomp (λ k → λ {(i = i1) → x
                 ; (i = i0) → (p1 (p1 x (~ k)) ∙∙ refl ∙∙ sym (p2 (p1 x (~ k)))) j
                 ; (j = i0) → p1 x i
                 ; (j = i1) → p2 x i})
        (hcomp (λ k → λ {(i = i1) → x
                        ; (j = i0) → p1 x (i ∨ ~ k)
                        ; (j = i1) → p2 x (i ∨ ~ k) })
               x)
-}

{-
Goal: A
j = i0 ⊢ p1 x i
j = i1 ⊢ p2 x i
i = i0 ⊢ (p1 c1 ∙∙ refl ∙∙ sym (p2 c1)) j
i = i1 ⊢ x
-}




-- Exercises about Part 3:

-- Exercise 8 (a bit longer, but very good):

open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (addEq ; subEq)

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.

-- a) Define a path "addEq n" by composing sucPathInt with itself n
-- times.
addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathInt

-- b) Define another path "subEq n" by composing "sym sucPathInt" with
-- itself n times.
subEq : ℕ → Int ≡ Int
subEq zero = refl
subEq (suc n) = (subEq n) ∙ sym sucPathInt


-- c) Define addition on integers by pattern-matching and transporting
-- along addEq/subEq appropriately.
_+Int_ : Int → Int → Int
m +Int pos n    = transport (addEq n) m
m +Int negsuc n = transport (subEq (suc n)) m

-- d) Do some concrete computations using _+Int_ (this would not work
-- in HoTT as the transport would be stuck!)


-- Exercise 9: prove that hSet is not an hSet

open import Cubical.Data.Bool renaming (notEq to notPath)
open import Cubical.Data.Empty

-- Just define hSets of level 0 for simplicity
hSet : Type₁
hSet = Σ[ A ∈ Type₀ ] isSet A

-- Bool is an hSet
BoolSet : hSet
BoolSet = Bool , isSetBool

notPath≢refl : (notPath ≡ refl) → ⊥
notPath≢refl e = true≢false (transport (λ i → transport (e i) true ≡ false) refl)

¬isSet-hSet : isSet hSet → ⊥
¬isSet-hSet h = notPath≢refl (cong (cong fst) (h BoolSet BoolSet {!!} refl))




-- Exercise 10 (more work): prove that FinData and Fin are equivalent
-- and hence equal. Transport some functions and proofs between the
-- two.

open import Cubical.Data.Nat.Order

data FinData : ℕ → Type₀ where
  zero : {n : ℕ} → FinData (suc n)
  suc  : {n : ℕ} (i : FinData n) → FinData (suc n)

Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k < n

open import Cubical.HITs.S1
open import Cubical.Data.Int
open import Cubical.HITs.Susp
open import Cubical.Data.Bool
Silly : Susp Bool → Type₀
Silly north = T'
  module _ where
    data T' : Type₀ where
      inc : ΩS¹ → T'
Silly south = W'
  module _ where
    data W' : Type₀ where
      inc : Int → W'
Silly (merid a i) = {!WW'!}
    module _ where
    data WW' : Type₀ where
      inc : (ΩS¹≡Int i) → WW'
