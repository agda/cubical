{-

This file contains:
  -- Path lemmas used in the colimit equivalence proof.

Very long, indeed. But should be simple.
The length mainly thanks to:
  -- Refls, lots of refls, and they lead to much degeneracy.
     Maybe one has regularity or something could make them all trivial;

  -- No pattern matching for J rule or any sytactically convenient way
     to apply it. So when you deal with complicated composite functions
     it needs to many helper functions.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level


-- Lots of degenerate cubes for applying J rule

private
  module _
    {A : Type ℓ}{B : Type ℓ'}(a : A)(f : A → B) where

    degenerate1 : (i j k : I) → A
    degenerate1 i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl k j
        ; (j = i0) → a
        ; (j = i1) → a})
      (inS a) k

    degenerate1' : (i j k : I) → A
    degenerate1' i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → compPath-filler (refl {x = a}) refl k j
        ; (j = i0) → a
        ; (j = i1) → a})
      (inS a) k

    degenerate1'' : (i j k : I) → A
    degenerate1'' i j k =
      hfill (λ k → λ
        { (i = i0) → a
        ; (i = i1) → compPath-filler (refl {x = a}) (refl ∙ refl) k j
        ; (j = i0) → a
        ; (j = i1) → degenerate1 i k i1})
      (inS a) k

    degenerate2 : (i j k : I) → B
    degenerate2 i j k =
      hfill (λ k → λ
        { (i = i0) → f a
        ; (i = i1) → doubleCompPath-filler (refl {x = f a}) refl refl k j
        ; (j = i0) → f a
        ; (j = i1) → f a })
      (inS (f a)) k

    degenerate3 : (i j k : I) → B
    degenerate3 i j k =
      hfill (λ k → λ
        { (i = i0) → f (doubleCompPath-filler (refl {x = a}) refl refl k j)
        ; (i = i1) → doubleCompPath-filler (refl {x = f a}) refl refl k j
        ; (j = i0) → f a
        ; (j = i1) → f a })
      (inS (f a)) k

    degenerate4 : (i j k : I) → A
    degenerate4 i j k =
      hfill (λ k → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl j k
        ; (j = i0) → a
        ; (j = i1) → (refl {x = a} ∙∙ refl ∙∙ refl) k })
      (inS a) k

    degenerate5 :
      SquareP
        (λ i j → a ≡ degenerate4 i j i1)
        (λ i j → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) j i)
        (λ i j → a) (λ i j → a)
        (λ i j → doubleCompPath-filler (refl {x = a}) refl refl (~ i) j)
    degenerate5 i j k =
      hcomp (λ l → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl (j ∧ ~ l) k
        ; (j = i0) → a
        ; (j = i1) → doubleCompPath-filler (refl {x = a}) refl refl (~ i ∨ ~ l) k
        ; (k = i0) → a
        ; (k = i1) → degenerate4 i j i1 })
      (degenerate4 i j k)

    degenerate5' :
      (i j k : I) → A
    degenerate5' i j k =
      hfill (λ k → λ
        { (i = i0) → doubleCompPath-filler (refl {x = a}) refl (refl ∙ refl) k j
        ; (i = i1) → a
        ; (j = i0) → a
        ; (j = i1) → compPath-filler (refl {x = a}) refl (~ i) k })
      (inS a) k

    someCommonDegenerateCube :
      (i j k : I) → B
    someCommonDegenerateCube i j k =
      hcomp (λ l → λ
        { (i = i0) → f a
        ; (i = i1) → degenerate3 k j l
        ; (j = i0) → f a
        ; (j = i1) → f a
        ; (k = i0) → f (degenerate1 i j l)
        ; (k = i1) → degenerate2 i j l })
      (f a)


coh-helper-refl : {A : Type ℓ}{a : A}(q' : a ≡ a)
  → refl ≡ q'
  → refl ≡ refl ∙∙ refl ∙∙ q'
coh-helper-refl {a = a} q' h i j =
  hcomp (λ k → λ
    { (i = i0) → a
    ; (i = i1) → doubleCompPath-filler refl refl q' k j
    ; (j = i0) → a
    ; (j = i1) → h i k })
  a

coh-helper' : {A : Type ℓ}{a c : A}(q q' : a ≡ c)
  → PathP (λ i → a ≡ q i) refl q'
  → refl ≡ (sym q) ∙∙ refl ∙∙ q'
coh-helper' {a = a} =
  J (λ c q → (q' : a ≡ c) → PathP (λ i → a ≡ q i) refl q' → refl ≡ (sym q) ∙∙ refl ∙∙ q')
    coh-helper-refl

coh-helper : {A : Type ℓ}{a b c : A}(p : a ≡ b)(q q' : b ≡ c)
  → PathP (λ i → p i ≡ q i) p q'
  → refl ≡ (sym q) ∙∙ refl ∙∙ q'
coh-helper {A = A} {a = a} p =
  J (λ b p → {c : A}(q q' : b ≡ c) → PathP (λ i → p i ≡ q i) p q' → refl ≡ (sym q) ∙∙ refl ∙∙ q')
    coh-helper' p

coh-helper-Refl : {A : Type ℓ}{a : A}
    (q' : a ≡ a)
  → (sqr : refl ≡ q')
  → coh-helper-refl q' sqr ≡ coh-helper refl refl q' sqr
coh-helper-Refl {A = A} {a = a} q' sqr = sym (
    (λ i → JRefl (λ b p → {c : A}(q q' : b ≡ c) → PathP (λ i → p i ≡ q i) p q' → refl ≡ (sym q) ∙∙ refl ∙∙ q')
      coh-helper' i refl q' sqr)
  ∙ (λ i → JRefl (λ c q → (q' : a ≡ c) → PathP (λ i → a ≡ q i) refl q' → refl ≡ (sym q) ∙∙ refl ∙∙ q')
      coh-helper-refl i q' sqr))


doubleCompPath-cong-filler : {A : Type ℓ}{B : Type ℓ'}
    {a b c d : A}{a' b' c' d' : B}
    (f : A → B)
  → {pa : f a ≡ a'}{pb : f b ≡ b'}{pc : f c ≡ c'}{pd : f d ≡ d'}
  → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
  → {p' : a' ≡ b'}{q' : b' ≡ c'}{r' : c' ≡ d'}
  → (h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
  → (h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
  → (h'' : PathP (λ i → pc i ≡ pd i) (cong f r) r')
  → (i j k : I) → B
doubleCompPath-cong-filler f p q r {p' = p'} {q' = q'} {r' = r'}  h h' h'' i j k =
  hfill (λ k → λ
    { (i = i0) → f (doubleCompPath-filler p q r k j)
    ; (i = i1) → doubleCompPath-filler p' q' r' k j
    ; (j = i0) → h   i (~ k)
    ; (j = i1) → h'' i  k })
  (inS (h' i j)) k

doubleCompPath-cong : {A : Type ℓ}{B : Type ℓ'}{a b c d : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
  → cong f (p ∙∙ q ∙∙ r) ≡ cong f p ∙∙ cong f q ∙∙ cong f r
doubleCompPath-cong f p q r i j =
  doubleCompPath-cong-filler f
    {pa = refl} {pb = refl} {pc = refl} {pd = refl}
    p q r refl refl refl i j i1


comp-cong-square : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)
  → cong f (p ∙ q) ≡ cong f p ∙ cong f q
comp-cong-square {a = a} f p q i j =
  hcomp (λ k → λ
    { (i = i0) → f (compPath-filler p q k j)
    ; (i = i1) → compPath-filler (cong f p) (cong f q) k j
    ; (j = i0) → f a
    ; (j = i1) → f (q k) })
  (f (p j))

comp-cong-square' : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : a ≡ c)(r : b ≡ c)
  → (h : r ≡ sym p ∙∙ refl ∙∙ q)
  → p ∙ r ≡ q
comp-cong-square' {a = a} p q r h i j =
  hcomp (λ k → λ
    { (i = i0) → compPath-filler p r k j
    ; (i = i1) → doubleCompPath-filler (sym p) refl q j k
    ; (j = i0) → a
    ; (j = i1) → h i k })
  (p j)

comp-cong-helper-filler : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : f a ≡ f c)(r : b ≡ c)
  → (h : cong f r ≡ sym (cong f p) ∙∙ refl ∙∙ q)
  → (i j k : I) → B
comp-cong-helper-filler {a = a} {c = c} f p q r h i j k =
  hfill (λ k → λ
    { (i = i0) → comp-cong-square f p r (~ k) j
    ; (i = i1) → q j
    ; (j = i0) → f a
    ; (j = i1) → f c })
  (inS (comp-cong-square' _ _ _ h i j)) k

comp-cong-helper : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : f a ≡ f c)(r : b ≡ c)
  → (h : cong f r ≡ sym (cong f p) ∙∙ refl ∙∙ q)
  → cong f (p ∙ r) ≡ q
comp-cong-helper {a = a} f p q r h i j =
  comp-cong-helper-filler f p q r h i j i1


push-helper-refl : {A : Type ℓ}{c : A} → (q' : c ≡ c)
  → refl ≡ q'
  → refl ≡ refl ∙ q'
push-helper-refl {c = c} q' h i j =
  hcomp (λ k → λ
    { (i = i0) → c
    ; (i = i1) → compPath-filler refl q' k j
    ; (j = i0) → c
    ; (j = i1) → h i k })
  c

push-helper' : {A : Type ℓ}{a c : A} → (q : a ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → PathP (λ i → a ≡ q i) refl (q ∙ q')
push-helper' {a = a} =
  J (λ c q → (q' : c ≡ c) → refl ≡ q' → PathP (λ i → a ≡ q i) refl (q ∙ q'))
    push-helper-refl

push-helper : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → refl ≡ q'
  → PathP (λ i → p i ≡ q i) p (q ∙ q')
push-helper {A = A} p =
  J (λ b p → {c : A}(q : b ≡ c)(q' : c ≡ c) → refl ≡ q' → PathP (λ i → p i ≡ q i) p (q ∙ q'))
    push-helper' p

push-helper-Refl : {A : Type ℓ}{c : A}
    (q' : c ≡ c)
  → (h : refl ≡ q')
  → push-helper-refl q' h ≡ push-helper refl refl q' h
push-helper-Refl {A = A} {c = a} q' h = sym (
    (λ i → JRefl (λ b p → {c : A}(q : b ≡ c)(q' : c ≡ c) → refl ≡ q' → PathP (λ i → p i ≡ q i) p (q ∙ q'))
      push-helper' i refl q' h)
  ∙ (λ i → JRefl (λ c q → (q' : c ≡ c) → refl ≡ q' → PathP (λ i → a ≡ q i) refl (q ∙ q'))
      push-helper-refl i q' h))


module _
  {A : Type ℓ}{B : Type ℓ'}{a : A}(f : A → B) where

    push-helper-cong-refl' :
      SquareP
        (λ i j → f (push-helper-refl _ (λ i j → a) i j)
          ≡ push-helper-refl _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → comp-cong-square f (refl {x = a}) refl j i)
        (λ i j → f a) (λ i j → f a)
    push-helper-cong-refl' i j k =
      someCommonDegenerateCube a f i j k

    push-helper-cong-refl :
      SquareP
        (λ i j → f (push-helper refl refl _ (λ i j → a) i j)
          ≡ push-helper refl refl _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → comp-cong-square f (refl {x = a}) refl j i)
        (λ i j → f a) (λ i j → f a)
    push-helper-cong-refl =
      transport (λ t →
        SquareP
          (λ i j → f (push-helper-Refl _ (λ i j → a) t i j)
            ≡ push-helper-Refl _ (λ i j → f a) t i j)
          (λ i j → f a)
          (λ i j → comp-cong-square f (refl {x = a}) refl j i)
          (λ i j → f a) (λ i j → f a)) push-helper-cong-refl'

    push-helper-cong-ind1 :
      (b : A)(p : a ≡ b) → Type (ℓ-max ℓ ℓ')
    push-helper-cong-ind1 b p =
        (c : A)(q : b ≡ c)
        (q' : c ≡ c)
      → (sqr : refl ≡ q')
      → SquareP
        (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
        (λ i j → f (p i))
        (λ i j → comp-cong-square f q q' j i)
        (λ i j → f (p i)) (λ i j → f (q i))

    push-helper-cong-ind2 :
      (c : A)(q : a ≡ c) → Type (ℓ-max ℓ ℓ')
    push-helper-cong-ind2 c q =
      let b = a ; p = refl {x = a} in
        (q' : c ≡ c)
      → (sqr : refl ≡ q')
      → SquareP
        (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
        (λ i j → f (p i))
        (λ i j → comp-cong-square f q q' j i)
        (λ i j → f (p i)) (λ i j → f (q i))

    push-helper-cong-ind3 :
      (q' : a ≡ a)(sqr : refl ≡ q') → Type ℓ'
    push-helper-cong-ind3 q' sqr =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a} in
        SquareP
        (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
        (λ i j → f (p i))
        (λ i j → comp-cong-square f q q' j i)
        (λ i j → f (p i)) (λ i j → f (q i))

    push-helper-cong' :
        (b : A)(p : a ≡ b)
        (c : A)(q : b ≡ c)
        (q' : c ≡ c)(sqr : refl ≡ q')
      → SquareP
        (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
        (λ i j → f (p i))
        (λ i j → comp-cong-square f q q' j i)
        (λ i j → f (p i)) (λ i j → f (q i))
    push-helper-cong' _ =
      J push-helper-cong-ind1 (λ _ →
        J push-helper-cong-ind2 (λ _ →
          J push-helper-cong-ind3 push-helper-cong-refl))

push-helper-cong : {A : Type ℓ}{B : Type ℓ'}{a b c : A}
    (f : A → B)
  → (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → (sqr : refl ≡ q')
  → SquareP
      (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
      (λ i j → f (p i))
      (λ i j → comp-cong-square f q q' j i)
      (λ i j → f (p i)) (λ i j → f (q i))
push-helper-cong f p q q' sqr = push-helper-cong' f _ p _ q q' sqr


module _
  {A : Type ℓ}{a : A} where

  push-coh-helper-refl' :
    SquareP
      (λ i j → push-helper-refl _ (coh-helper-refl _ (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a)
      (λ i j → a)
  push-coh-helper-refl' i j k =
    hcomp (λ l → λ
      { (i = i0) → a
      ; (i = i1) → degenerate5 a (idfun _) k j l
      ; (j = i0) → a
      ; (j = i1) → degenerate1 a (idfun _) i l (~ k)
      ; (k = i0) → degenerate1'' a (idfun _) i j l
      ; (k = i1) → a })
    a

  push-coh-helper-refl :
    SquareP
      (λ i j → push-helper refl refl _ (coh-helper _ _ _ (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a)
      (λ i j → a)
  push-coh-helper-refl =
    transport (λ t →
      SquareP
      (λ i j → push-helper-Refl _ (coh-helper-Refl _ (λ i j → a) t) t i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a) (λ i j → a)) push-coh-helper-refl'

  push-coh-helper-ind1 :
    (b : A)(p : a ≡ b) → Type ℓ
  push-coh-helper-ind1 b p =
      (c : A)(q : b ≡ c)
      (q' : b ≡ c)(sqr : PathP (λ i → p i ≡ q i) p q')
    → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)

  push-coh-helper-ind2 :
    (c : A)(q : a ≡ c) → Type ℓ
  push-coh-helper-ind2 c q =
    let b = a ; p = refl {x = a} in
      (q' : b ≡ c)(sqr : PathP (λ i → p i ≡ q i) p q')
    → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)

  push-coh-helper-ind3 :
    (q' : a ≡ a)(sqr : PathP (λ i → a ≡ a) refl q') → Type ℓ
  push-coh-helper-ind3 q' sqr =
    let b = a ; p = refl {x = a}
        c = a ; q = refl {x = a} in
      SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)

  push-coh-helper' :
      (b : A)(p : a ≡ b)
      (c : A)(q : b ≡ c)
      (q' : b ≡ c)(sqr : PathP (λ i → p i ≡ q i) p q')
    → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)
  push-coh-helper' _ =
    J push-coh-helper-ind1 (λ _ →
      J push-coh-helper-ind2 (λ _ →
        J push-coh-helper-ind3 push-coh-helper-refl))

push-coh-helper : {A : Type ℓ}{a b c : A}
    (p : a ≡ b)(q q' : b ≡ c)
  → (sqr : PathP (λ i → p i ≡ q i) p q')
  → SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i)
      (λ i j → q i)
push-coh-helper p q q' sqr = push-coh-helper' _ p _ q q' sqr


push-square-helper-refl : {A : Type ℓ}{a : A}
  → refl ∙∙ refl ∙∙ (refl ∙ refl) ≡ refl {x = a}
push-square-helper-refl {a = a} i j = degenerate5' a (idfun _) i j i1

push-square-helper' : {A : Type ℓ}{a c : A}
  → (q' : a ≡ c)
  → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q'
push-square-helper' {a = a} =
  J (λ _ q' → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q') push-square-helper-refl

push-square-helper : {A : Type ℓ}{a b c : A}
  → (q : a ≡ b)(q' : b ≡ c)
  → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q'
push-square-helper {A = A} p =
  J (λ b q → {c : A}(q' : b ≡ c) → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q') push-square-helper' p

push-square-helper-Refl : {A : Type ℓ}{a : A}
  → push-square-helper-refl {a = a} ≡ push-square-helper refl refl
push-square-helper-Refl {A = A} = sym (
    (λ i → JRefl (λ b q → {c : A}(q' : b ≡ c) → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q')
      push-square-helper' i refl)
  ∙ (λ i → JRefl (λ _ q' → refl ∙∙ refl ∙∙ (refl ∙ q') ≡ q')
      push-square-helper-refl i))


module _
  {A : Type ℓ}{a : A} where

  coh-cube-helper-refl' :
    SquareP
      (λ i j → coh-helper-refl _ (push-helper-refl refl (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → push-square-helper-refl {a = a} j i)
      (λ i j → a) (λ i j → a)
  coh-cube-helper-refl' i j k =
    hcomp (λ l → λ
      { (i = i0) → a
      ; (i = i1) → degenerate5' a (idfun _) k j l
      ; (j = i0) → a
      ; (j = i1) → degenerate1' a (idfun _) i l (~ k)
      ; (k = i0) → degenerate1'' a (idfun _) i j l
      ; (k = i1) → a })
    a

  coh-cube-helper-refl :
    SquareP
      (λ i j → coh-helper _ _ _ (push-helper refl refl refl (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → push-square-helper (refl {x = a}) refl j i)
      (λ i j → a) (λ i j → a)
  coh-cube-helper-refl =
    transport (λ t →
      SquareP
      (λ i j → coh-helper-Refl _ (push-helper-Refl refl (λ i j → a) t) t i j ≡ a)
      (λ i j → a)
      (λ i j → push-square-helper-Refl {a = a} t j i)
      (λ i j → a) (λ i j → a)) coh-cube-helper-refl'

  coh-cube-helper-ind1 :
    (b : A)(p : a ≡ b) → Type ℓ
  coh-cube-helper-ind1 b p =
      (c : A)(q : b ≡ c)
      (q' : c ≡ c)(sqr : refl ≡ q')
    → SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c) (λ i j → c)

  coh-cube-helper-ind2 :
    (c : A)(q : a ≡ c) → Type ℓ
  coh-cube-helper-ind2 c q =
    let b = a ; p = refl {x = a} in
      (q' : c ≡ c)(sqr : refl ≡ q')
    → SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c) (λ i j → c)

  coh-cube-helper-ind3 :
    (q' : a ≡ a)(sqr : refl ≡ q') → Type ℓ
  coh-cube-helper-ind3 q' sqr =
    let b = a ; p = refl {x = a}
        c = a ; q = refl {x = a} in
      SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c) (λ i j → c)

  coh-cube-helper' :
      (b : A)(p : a ≡ b)
      (c : A)(q : b ≡ c)
      (q' : c ≡ c)(sqr : refl ≡ q')
    → SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c) (λ i j → c)
  coh-cube-helper' _ =
    J coh-cube-helper-ind1 (λ _ →
        J coh-cube-helper-ind2 (λ _ →
          J coh-cube-helper-ind3 coh-cube-helper-refl))


coh-cube-helper : {A : Type ℓ}{a b c : A} → (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)
  → (sqr : refl ≡ q')
  → SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c)
      (λ i j → c)
coh-cube-helper p q q' sqr = coh-cube-helper' _ p _ q q' sqr


-- Awwwwwwwwwwww
-- The following uses J rule TEN times iteratively.
-- Actually the proof is rather easy, if only one has regularity
--  or at least some syntactic sugar to iteratively apply J rule.
-- But no, so it is extremely long.
-- Awwwwwwwwwwww

private
  module _
    {A : Type ℓ}{B : Type ℓ'}{a : A}(f : A → B) where

    coh-helper-cong-refl' :
      SquareP
        (λ i j → f (coh-helper-refl _ (λ i j → a) i j) ≡ coh-helper-refl _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → doubleCompPath-cong-filler f refl refl refl (λ i j → f a) (λ i j → f a) (λ i j → f a) j i i1)
        (λ i j → f a)
        (λ i j → f a)
    coh-helper-cong-refl' i j k =
      someCommonDegenerateCube a f i j k

    coh-helper-cong-refl :
      SquareP
        (λ i j → f (coh-helper _ _ _ (λ i j → a) i j) ≡ coh-helper _ _ _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → doubleCompPath-cong-filler f refl refl refl (λ i j → f a) (λ i j → f a) (λ i j → f a) j i i1)
        (λ i j → f a)
        (λ i j → f a)
    coh-helper-cong-refl =
      transport (λ t →
        SquareP
        (λ i j → f (coh-helper-Refl _ (λ i j → a) t i j) ≡ coh-helper-Refl _ (λ i j → f a) t i j)
        (λ i j → f a)
        (λ i j → doubleCompPath-cong-filler f refl refl refl (λ i j → f a) (λ i j → f a) (λ i j → f a) j i i1)
        (λ i j → f a)
        (λ i j → f a)) coh-helper-cong-refl'

    ind1 :
      (b : A)(p : a ≡ b) → Type (ℓ-max ℓ ℓ')
    ind1 b p =
      (c : A)(q : b ≡ c)
      (a' : B)(pa : f a ≡ a')
      (b' : B)(pb : f b ≡ b')
      (c' : B)(pc : f c ≡ c')
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : a' ≡ b')(h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind2 :
      (c : A)(q : a ≡ c) → Type (ℓ-max ℓ ℓ')
    ind2 c q =
      let b = a ; p = refl {x = a} in
      (a' : B)(pa : f a ≡ a')
      (b' : B)(pb : f b ≡ b')
      (c' : B)(pc : f c ≡ c')
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : a' ≡ b')(h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind3 :
      (a' : B)(pa : f a ≡ a') → Type (ℓ-max ℓ ℓ')
    ind3 a' pa =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a} in
      (b' : B)(pb : f b ≡ b')
      (c' : B)(pc : f c ≡ c')
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : a' ≡ b')(h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind4 :
      (b' : B)(pb : f a ≡ b') → Type (ℓ-max ℓ ℓ')
    ind4 b' pb =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a} in
      (c' : B)(pc : f c ≡ c')
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : a' ≡ b')(h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind5 :
      (c' : B)(pc : f a ≡ c') → Type (ℓ-max ℓ ℓ')
    ind5 c' pc =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a} in
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : f a ≡ b')(h   : PathP (λ i → f a ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind6 :
      (r : a ≡ a)(sqr : PathP (λ i → a ≡ a) refl r) → Type ℓ'
    ind6 r sqr =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a}
          c' = f a ; pc = refl {x = f a} in
      (p' : f a ≡ b')(h   : PathP (λ i → f a ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind7 :
      (p' : f a ≡ f a)(h : PathP (λ i → f a ≡ f a) refl p') → Type ℓ'
    ind7 p' h =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a}
          c' = f a ; pc = refl {x = f a}
          r  = refl {x = a} ; sqr = refl {x = r} in
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind8 :
      (q' : f a ≡ f a)(h' : PathP (λ i → f a ≡ f a) refl q') → Type ℓ'
    ind8 q' h' =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a}
          c' = f a ; pc = refl {x = f a}
          r  = refl {x = a} ; sqr = refl {x = r}
          p' = refl {x = f a} ; h = refl {x = p'} in
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind9 :
      (r' : f a ≡ f a)(h'' : PathP (λ i → f a ≡ f a) refl r') → Type ℓ'
    ind9 r' h'' =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a}
          c' = f a ; pc = refl {x = f a}
          r  = refl {x = a} ; sqr = refl {x = r}
          p' = refl {x = f a} ; h  = refl {x = p'}
          q' = refl {x = f a} ; h' = refl {x = q'} in
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind10 :
      (sqr' : PathP (λ i → f a ≡ f a) refl refl)
      (hsqr : SquareP (λ i j → f a ≡ sqr' i j)
        (λ i j → f a) (λ i j → f a) (λ i j → f a) (λ i j → f a)) → Type ℓ'
    ind10 sqr' hsqr =
      let b = a ; p = refl {x = a}
          c = a ; q = refl {x = a}
          a' = f a ; pa = refl {x = f a}
          b' = f a ; pb = refl {x = f a}
          c' = f a ; pc = refl {x = f a}
          r  = refl {x = a} ; sqr = refl {x = r}
          p' = refl {x = f a} ; h   = refl {x = p'}
          q' = refl {x = f a} ; h'  = refl {x = q'}
          r' = refl {x = f a} ; h'' = refl {x = q'} in
        SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)

    ind10' :
      (sqr' : PathP (λ i → f a ≡ f a) refl refl)
      (hsqr : refl ≡ sqr') → Type ℓ'
    ind10' sqr' hsqr =
      SquareP
        (λ i j → f (coh-helper _ _ _ (λ i j → a) i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
        (λ i j → f a)
        (λ i j → doubleCompPath-cong-filler f refl refl refl (λ i j → f a) (λ i j → f a) (λ i j → f a) j i i1)
        (λ i j → f a) (λ i j → f a)

    ind10'→ind10 :
        (∀ x y → ind10' x y)
      → ∀ x y → ind10 x y
    ind10'→ind10 f sqr' hsqr = f sqr' (λ i j k → hsqr j k i)

    coh-helper-cong' :
      (b : A)(p : a ≡ b)
      (c : A)(q : b ≡ c)
      (a' : B)(pa : f a ≡ a')
      (b' : B)(pb : f b ≡ b')
      (c' : B)(pc : f c ≡ c')
      (r : b ≡ c)(sqr  : PathP (λ i → p  i ≡ q  i) p r)
      (p' : a' ≡ b')(h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
      (q' : b' ≡ c')(h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
      (r' : b' ≡ c')(h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
      (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
      (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
        (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
      → SquareP
          (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
          (λ i j → pc j)
          (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
          (λ i j → pc j)
          (λ i j → pc j)
    coh-helper-cong' _ =
      J ind1 (λ _ →
        J ind2 (λ _ →
          J ind3 (λ _ →
            J ind4 (λ _ →
              J ind5 (λ _ →
                J ind6 (λ _ →
                  J ind7 (λ _ →
                    J ind8 (λ _ →
                      J ind9
                        (ind10'→ind10 (λ _ →
                          J ind10' coh-helper-cong-refl))))))))))


coh-helper-cong : {A : Type ℓ}{B : Type ℓ'}{a b c : A}{a' b' c' : B}
    (f : A → B)
  → {pa : f a ≡ a'}{pb : f b ≡ b'}{pc : f c ≡ c'}
  → (p  : a  ≡ b )(q  r  : b  ≡ c )
  → {p' : a' ≡ b'}{q' r' : b' ≡ c'}
  → {h   : PathP (λ i → pa i ≡ pb i) (cong f p) p'}
  → {h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q'}
  → {h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r'}
  → (sqr  : PathP (λ i → p  i ≡ q  i) p  r)
  → {sqr' : PathP (λ i → p' i ≡ q' i) p' r'}
  → (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
              (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
  → SquareP
      (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
      (λ i j → pc j)
      (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
      (λ i j → pc j)
      (λ i j → pc j)
coh-helper-cong f p q r sqr hsqr =
  coh-helper-cong' f _ p _ q _ _ _ _ _ _ r sqr _ _ _ _ _ _ _ hsqr
