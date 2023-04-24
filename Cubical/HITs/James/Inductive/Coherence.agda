{-

This file contains:
  - Path lemmas used in the colimit-equivalence proof.

Verbose, indeed. But should be simple. The length mainly thanks to:
  - Degenerate cubes that seem "obvious", but have to be constructed manually;
  - J rule is cubersome to use, especially when iteratively applied,
    also it is overcomplicated to construct JRefl in nested cases.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.HITs.James.Inductive.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level


-- Lots of degenerate cubes used as intial input to J rule

private
  module _
    {A : Type ℓ}(a : A) where

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

    module _
      {B : Type ℓ'}(f : A → B) where

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

      someCommonDegenerateCube : (i j k : I) → B
      someCommonDegenerateCube i j k =
        hcomp (λ l → λ
          { (i = i0) → f a
          ; (i = i1) → degenerate3 k j l
          ; (j = i0) → f a
          ; (j = i1) → f a
          ; (k = i0) → f (degenerate1 i j l)
          ; (k = i1) → degenerate2 i j l })
        (f a)

    degenerate4 : (i j k : I) → A
    degenerate4 i j k =
      hfill (λ k → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl j k
        ; (j = i0) → a
        ; (j = i1) → (refl {x = a} ∙∙ refl ∙∙ refl) k })
      (inS a) k

    degenerate5 : (i j k : I) → A
    degenerate5 i j k =
      hcomp (λ l → λ
        { (i = i0) → compPath-filler (refl {x = a}) (refl ∙∙ refl ∙∙ refl) k j
        ; (i = i1) → doubleCompPath-filler (refl {x = a}) refl refl (j ∧ ~ l) k
        ; (j = i0) → a
        ; (j = i1) → doubleCompPath-filler (refl {x = a}) refl refl (~ i ∨ ~ l) k
        ; (k = i0) → a
        ; (k = i1) → degenerate4 i j i1 })
      (degenerate4 i j k)

    degenerate5' : (i j k : I) → A
    degenerate5' i j k =
      hfill (λ k → λ
        { (i = i0) → doubleCompPath-filler (refl {x = a}) refl (refl ∙ refl) k j
        ; (i = i1) → a
        ; (j = i0) → a
        ; (j = i1) → compPath-filler (refl {x = a}) refl (~ i) k })
      (inS a) k


-- Cubes of which mostly are constructed by J rule

module _
  {A : Type ℓ}{a : A} where

  coh-helper-refl :
    (q' : a ≡ a)(h : refl ≡ q')
    → refl ≡ refl ∙∙ refl ∙∙ q'
  coh-helper-refl q' h i j =
    hcomp (λ k → λ
      { (i = i0) → a
      ; (i = i1) → doubleCompPath-filler refl refl q' k j
      ; (j = i0) → a
      ; (j = i1) → h i k })
    a

  coh-helper' :
    (b : A)(p : a ≡ b)
    (c : A)(q : b ≡ c)
    (q' : b ≡ c)(r : PathP (λ i → p i ≡ q i) p q')
    → refl ≡ (sym q) ∙∙ refl ∙∙ q'
  coh-helper' = J> J> coh-helper-refl

  coh-helper'-Refl1 : coh-helper' _ refl ≡ J> coh-helper-refl
  coh-helper'-Refl1 = transportRefl _

  coh-helper'-Refl2 : coh-helper' _ refl _ refl ≡ coh-helper-refl
  coh-helper'-Refl2 = (λ i → coh-helper'-Refl1 i _ refl) ∙ transportRefl _

  coh-helper :
    {b c : A}(p : a ≡ b)(q q' : b ≡ c)
    (h : PathP (λ i → p i ≡ q i) p q')
    → refl ≡ (sym q) ∙∙ refl ∙∙ q'
  coh-helper p = coh-helper' _ p _

  coh-helper-Refl : coh-helper-refl ≡ coh-helper refl refl
  coh-helper-Refl = sym coh-helper'-Refl2


module _
  {A : Type ℓ}{B : Type ℓ'}{a b c d : A} where

  doubleCompPath-cong-filler :
    {a' b' c' d' : B} (f : A → B)
    {pa : f a ≡ a'}{pb : f b ≡ b'}{pc : f c ≡ c'}{pd : f d ≡ d'}
    (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
    {p' : a' ≡ b'}{q' : b' ≡ c'}{r' : c' ≡ d'}
    (h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
    (h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
    (h'' : PathP (λ i → pc i ≡ pd i) (cong f r) r')
    → (i j k : I) → B
  doubleCompPath-cong-filler f p q r {p' = p'} {q' = q'} {r' = r'}  h h' h'' i j k =
    hfill (λ k → λ
      { (i = i0) → f (doubleCompPath-filler p q r k j)
      ; (i = i1) → doubleCompPath-filler p' q' r' k j
      ; (j = i0) → h   i (~ k)
      ; (j = i1) → h'' i  k })
    (inS (h' i j)) k

  doubleCompPath-cong : (f : A → B)
    (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
    → cong f (p ∙∙ q ∙∙ r) ≡ cong f p ∙∙ cong f q ∙∙ cong f r
  doubleCompPath-cong f p q r i j =
    doubleCompPath-cong-filler f
      {pa = refl} {pb = refl} {pc = refl} {pd = refl}
      p q r refl refl refl i j i1


module _
  {A : Type ℓ}{a b c : A} where

  comp-cong-square' :
    (p : a ≡ b)(q : a ≡ c)
    (r : b ≡ c)(h : r ≡ sym p ∙∙ refl ∙∙ q)
    → p ∙ r ≡ q
  comp-cong-square' p q r h i j =
    hcomp (λ k → λ
      { (i = i0) → compPath-filler p r k j
      ; (i = i1) → doubleCompPath-filler (sym p) refl q j k
      ; (j = i0) → a
      ; (j = i1) → h i k })
    (p j)

  module _
    {B : Type ℓ'} where

    comp-cong-square : (f : A → B)
      (p : a ≡ b)(q : b ≡ c)
      → cong f (p ∙ q) ≡ cong f p ∙ cong f q
    comp-cong-square f p q i j =
      hcomp (λ k → λ
        { (i = i0) → f (compPath-filler p q k j)
        ; (i = i1) → compPath-filler (cong f p) (cong f q) k j
        ; (j = i0) → f a
        ; (j = i1) → f (q k) })
      (f (p j))

module _
  {A : Type ℓ}{B : Type ℓ'}{a b c : A}
  (f : A → B)(p : a ≡ b)
  (q : f a ≡ f c)(r : b ≡ c)
  (h : cong f r ≡ sym (cong f p) ∙∙ refl ∙∙ q) where

  comp-cong-helper-filler : (i j k : I) → B
  comp-cong-helper-filler i j k =
    hfill (λ k → λ
      { (i = i0) → comp-cong-square f p r (~ k) j
      ; (i = i1) → q j
      ; (j = i0) → f a
      ; (j = i1) → f c })
    (inS (comp-cong-square' _ _ _ h i j)) k

  comp-cong-helper : cong f (p ∙ r) ≡ q
  comp-cong-helper i j =
    comp-cong-helper-filler i j i1


module _
  {A : Type ℓ}{a : A} where

  push-helper-refl :
    (q' : a ≡ a)(h : refl ≡ q')
    → refl ≡ refl ∙ q'
  push-helper-refl q' h i j =
    hcomp (λ k → λ
      { (i = i0) → a
      ; (i = i1) → compPath-filler refl q' k j
      ; (j = i0) → a
      ; (j = i1) → h i k })
    a

  push-helper' :
    (b : A)(p : a ≡ b)
    (c : A)(q : b ≡ c)
    (q' : c ≡ c)(h : refl ≡ q')
    → PathP (λ i → p i ≡ q i) p (q ∙ q')
  push-helper' = J> J> push-helper-refl

  push-helper'-Refl1 : push-helper' _ refl ≡ J> push-helper-refl
  push-helper'-Refl1 = transportRefl _

  push-helper'-Refl2 : push-helper' _ refl _ refl ≡ push-helper-refl
  push-helper'-Refl2 = (λ i → push-helper'-Refl1 i _ refl) ∙ transportRefl _

  push-helper : {b c : A}
    (p : a ≡ b)(q : b ≡ c)(q' : c ≡ c)(h : refl ≡ q')
    → PathP (λ i → p i ≡ q i) p (q ∙ q')
  push-helper p = push-helper' _ p _

  push-helper-Refl : push-helper-refl ≡ push-helper refl refl
  push-helper-Refl = sym push-helper'-Refl2


module _
  {A : Type ℓ}{B : Type ℓ'}{a : A}(f : A → B) where

  push-helper-cong-Type : {b c : A}
    (p : a ≡ b)(q : b ≡ c)
    (q' : c ≡ c)(sqr : refl ≡ q')
    → Type _
  push-helper-cong-Type p q q' sqr =
    SquareP
      (λ i j → f (push-helper p q _ sqr i j)
          ≡ push-helper (cong f p) (cong f q) _ (λ i j → f (sqr i j)) i j)
      (λ i j → f (p i))
      (λ i j → comp-cong-square f q q' j i)
      (λ i j → f (p i)) (λ i j → f (q i))

  push-helper-cong-refl : push-helper-cong-Type refl refl refl refl
  push-helper-cong-refl =
    transport (λ t →
      SquareP
        (λ i j → f (push-helper-Refl t _ (λ i j → a) i j)
          ≡ push-helper-Refl t _ (λ i j → f a) i j)
        (λ i j → f a)
        (λ i j → comp-cong-square f (refl {x = a}) refl j i)
        (λ i j → f a) (λ i j → f a))
        (λ i j k → someCommonDegenerateCube a f i j k)

  push-helper-cong' :
    (b : A)(p : a ≡ b)
    (c : A)(q : b ≡ c)
    (q' : c ≡ c)(sqr : refl ≡ q')
    → push-helper-cong-Type p q q' sqr
  push-helper-cong' = J> J> J> push-helper-cong-refl

  push-helper-cong : ∀ {b c} p q q' sqr → push-helper-cong-Type {b = b} {c = c} p q q' sqr
  push-helper-cong p = push-helper-cong' _ p _


module _
  {A : Type ℓ}{a : A} where

  push-coh-helper-Type : {b c : A}
    (p : a ≡ b)(q q' : b ≡ c)
    (sqr : PathP (λ i → p i ≡ q i) p q')
    → Type _
  push-coh-helper-Type p q q' sqr =
    SquareP
      (λ i j → push-helper p q _ (coh-helper _ _ _ sqr) i j ≡ sqr i j)
      (λ i j → p i)
      (λ i j → comp-cong-square' q q' _ refl j i)
      (λ i j → p i) (λ i j → q i)

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
      ; (i = i1) → degenerate5 a k j l
      ; (j = i0) → a
      ; (j = i1) → degenerate1 a i l (~ k)
      ; (k = i0) → degenerate1'' a i j l
      ; (k = i1) → a })
    a

  push-coh-helper-refl : push-coh-helper-Type refl refl refl refl
  push-coh-helper-refl =
    transport (λ t →
      SquareP
      (λ i j → push-helper-Refl t _ (coh-helper-Refl t _ (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → comp-cong-square' (refl {x = a}) refl _ refl j i)
      (λ i j → a) (λ i j → a)) push-coh-helper-refl'

  push-coh-helper' :
    (b : A)(p : a ≡ b)
    (c : A)(q : b ≡ c)
    (q' : b ≡ c)(sqr : PathP (λ i → p i ≡ q i) p q')
    → push-coh-helper-Type p q q' sqr
  push-coh-helper' = J> J> J> push-coh-helper-refl

  push-coh-helper : ∀ {b c} p q q' sqr → push-coh-helper-Type {b = b} {c = c} p q q' sqr
  push-coh-helper p q q' sqr = push-coh-helper' _ p _ q q' sqr


module _
  {A : Type ℓ}{a : A} where

  push-square-helper-refl :
    refl ∙∙ refl ∙∙ (refl ∙ refl) ≡ refl {x = a}
  push-square-helper-refl i j = degenerate5' a i j i1

  push-square-helper' :
    (b : A)(q  : a ≡ b)
    (c : A)(q' : b ≡ c)
    → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q'
  push-square-helper' = J> J> push-square-helper-refl

  push-square-helper'-Refl1 : push-square-helper' _ refl ≡ J> push-square-helper-refl
  push-square-helper'-Refl1 = transportRefl _

  push-square-helper'-Refl2 : push-square-helper' _ refl _ refl ≡ push-square-helper-refl
  push-square-helper'-Refl2 = (λ i → push-square-helper'-Refl1 i _ refl) ∙ transportRefl _

  push-square-helper : {b c : A}
    (q : a ≡ b)(q' : b ≡ c)
    → sym q ∙∙ refl ∙∙ (q ∙ q') ≡ q'
  push-square-helper p = push-square-helper' _ p _

  push-square-helper-Refl : push-square-helper-refl ≡ push-square-helper refl refl
  push-square-helper-Refl = sym push-square-helper'-Refl2


module _
  {A : Type ℓ}{a : A} where

  coh-cube-helper-Type :
    {b c : A}(p : a ≡ b)(q : b ≡ c)
    (q' : c ≡ c)(sqr : refl ≡ q')
    → Type _
  coh-cube-helper-Type {c = c} p q q' sqr =
    SquareP
      (λ i j → coh-helper _ _ _ (push-helper p q q' sqr) i j ≡ sqr i j)
      (λ i j → c)
      (λ i j → push-square-helper q q' j i)
      (λ i j → c) (λ i j → c)

  coh-cube-helper-refl' :
    SquareP
      (λ i j → coh-helper-refl _ (push-helper-refl refl (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → push-square-helper-refl {a = a} j i)
      (λ i j → a) (λ i j → a)
  coh-cube-helper-refl' i j k =
    hcomp (λ l → λ
      { (i = i0) → a
      ; (i = i1) → degenerate5' a k j l
      ; (j = i0) → a
      ; (j = i1) → degenerate1' a i l (~ k)
      ; (k = i0) → degenerate1'' a i j l
      ; (k = i1) → a })
    a

  coh-cube-helper-refl : coh-cube-helper-Type refl refl refl refl
  coh-cube-helper-refl =
    transport (λ t →
      SquareP
      (λ i j → coh-helper-Refl t _ (push-helper-Refl t refl (λ i j → a)) i j ≡ a)
      (λ i j → a)
      (λ i j → push-square-helper-Refl {a = a} t j i)
      (λ i j → a) (λ i j → a)) coh-cube-helper-refl'

  coh-cube-helper' :
    (b : A)(p : a ≡ b)
    (c : A)(q : b ≡ c)
    (q' : c ≡ c)(sqr : refl ≡ q')
    → coh-cube-helper-Type p q q' sqr
  coh-cube-helper' = J> J> J> coh-cube-helper-refl

  coh-cube-helper : ∀ {b c} p q q' sqr → coh-cube-helper-Type {b = b} {c = c} p q q' sqr
  coh-cube-helper p q q' sqr = coh-cube-helper' _ p _ q q' sqr


module _
  {A : Type ℓ}{B : Type ℓ'}{a : A}(f : A → B) where

  coh-helper-cong-Type : {b c : A}{a' b' c' : B}
    (pa : f a ≡ a')(pb : f b ≡ b')(pc : f c ≡ c')
    {p  : a  ≡ b }(q  r  : b  ≡ c )
    {p' : a' ≡ b'}{q' r' : b' ≡ c'}
    (h   : PathP (λ i → pa i ≡ pb i) (cong f p) p')
    (h'  : PathP (λ i → pb i ≡ pc i) (cong f q) q')
    (h'' : PathP (λ i → pb i ≡ pc i) (cong f r) r')
    (sqr  : PathP (λ i → p  i ≡ q  i) p  r)
    (sqr' : PathP (λ i → p' i ≡ q' i) p' r')
    → Type _
  coh-helper-cong-Type pa pb pc q r h h' h'' sqr sqr' =
    SquareP
      (λ i j → f (coh-helper _ _ _ sqr i j) ≡ coh-helper _ _ _ (λ i j → sqr' i j) i j)
      (λ i j → pc j)
      (λ i j → doubleCompPath-cong-filler f (sym q) refl r (λ i j → h' i (~ j)) (λ i j → pb i) h'' j i i1)
      (λ i j → pc j) (λ i j → pc j)

  coh-helper-cong-refl : coh-helper-cong-Type refl refl refl refl refl refl refl refl refl refl
  coh-helper-cong-refl =
    transport (λ t →
      SquareP
      (λ i j → f (coh-helper-Refl t _ (λ i j → a) i j) ≡ coh-helper-Refl t _ (λ i j → f a) i j)
      (λ i j → f a)
      (λ i j → doubleCompPath-cong-filler f refl refl refl (λ i j → f a) (λ i j → f a) (λ i j → f a) j i i1)
      (λ i j → f a) (λ i j → f a))
      (λ i j k → someCommonDegenerateCube a f i j k)

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
    (hsqr : SquareP (λ i j → h i j ≡ h' i j) (λ i j → f (sqr i j)) sqr' h h'')
    → coh-helper-cong-Type pa pb pc q r h h' h'' sqr sqr'
  coh-helper-cong' = J> J> J> J> J> J> J> J> J> J> coh-helper-cong-refl

  coh-helper-cong :
    ∀ {b c a' b' c' pa pb pc} p q r {p' q' r' h h' h''} sqr {sqr'}
    (hsqr : SquareP (λ i j → f (sqr i j) ≡ sqr' i j)
      (λ i j → h j i) (λ i j → h'' j i) (λ i j → h j i) (λ i j → h' j i))
    → coh-helper-cong-Type {b = b} {c = c} {a' = a'} {b' = b'} {c' = c'}
        pa pb pc q r {p' = p'} {q' = q'} {r' = r'} h h' h'' sqr sqr'
  coh-helper-cong p q r sqr hsqr =
    coh-helper-cong' _ p _ q _ _ _ _ _ _ r sqr _ _ _ _ _ _ _ (λ i j k → hsqr j k i)
