{-# OPTIONS --cubical #-}
module Cubical.Epit.Part2 where

{-
Part 3: Transport and composition
• Cubical transport
• Subst as a special case of cubical transport
• Path induction from subst
• Homogeneous composition (hcomp)
• Binary composition of paths as special case of hcomp
-}

open import Cubical.Epit.Part1 public

-- While path types are great for reasoning about equality they don't
-- let us transport along paths between types or even compose
-- paths. Furthermore, as paths are not inductively defined we don't
-- automatically get an induction principle for them. In order to
-- remedy this Cubical Agda also has a built-in (generalized)
-- transport operation and homogeneous composition operation from
-- which the induction principle (and much more!) is derivable.

-- The basic operation is called transp and we will soon explain it,
-- but let's first focus on a special case of cubical transport:
transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- This is a more primitive operation than "transport" in HoTT as it
-- only lets us turn a path into a function. However, the transport of
-- HoTT can easily be proved from cubical transport and in order to
-- avoid a name clash we call it "subst":
subst : (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

-- The transp operation is a generalized transport in the sense that
-- it lets us specify where the transport is the identity function.
-- The general type of transp is:
--
--   transp : (A : I → Type ℓ) (r : I) (a : A i0) → A i1
--
-- There is an additional side condition which to be satisfied for
-- Cubical Agda to typecheck "transp A r a". This is that A has to be
-- "constant" on r. This means that A should be a constant function
-- whenever r is i1 is satisfied. This side condition is vacuously
-- true when r is i0, so there is nothing to check when writing
-- transportas above. However, when r is equal to i1 the transp
-- function will compute as the identity function.
--
--   transp A i1 a = a
--
-- Having this extra generality is useful for quite technical reasons,
-- for instance we can easily relate a with its transport over p:
transportFill : (p : A ≡ B) (a : A) → PathP (λ i → p i) a (transport p a)
transportFill p a i = transp (λ j → p (i ∧ j)) (~ i) a

-- Another result that follows easily from transp is that transporting
-- in a constant family is the identity function (up to a path). Note
-- that this is *not* proved by refl. This is maybe not surprising as
-- transport is not defined by pattern-matching on p.
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

-- Having transp lets us prove many more useful lemmas like this. For
-- details see:
--
--   Cubical.Foundations.Transport
--
-- For experts: the file
--
--   Cubical.Foundations.CartesianKanOps
--
-- contains a reformulation of these operations which might be useful
-- for people familiar with "cartesian" cubical type theory.


-- We can also define the J eliminator (aka path induction)
J : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
    (d : P x refl) {y : A} (p : x ≡ y) → P y p
J {x = x} P d p = subst (λ X → P (fst X) (snd X)) (isContrSingl x .snd (_ , p)) d

-- Unfolded version:
-- transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- So J is provable, but it doesn't satisfy computation rule
-- definitionally as _≡_ is not inductively defined. See exercises for
-- how to prove it. Not having this hold definitionally is almost
-- never a problem in practice as the cubical primitives satisfy many
-- new definitional equalities (c.f. cong).

-- As we now have J we can define path concatenation and many more
-- things, however this is not the way to do things in Cubical
-- Agda. One of the key features of cubical type theory is that the
-- transp primitive reduces differently for different types formers
-- (see CCHM or the Cubical Agda paper for details). For paths it
-- reduces to another primitive operation called hcomp. This primitive
-- is much better suited for concatenating paths and more generally,
-- for composing multiple higher dimensional cubes. We will explain it
-- by example.

-- In order to compose two paths we write:

compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

-- This is best understood with the following drawing:
--
--     x             z
--     ^             ^
--     ¦             ¦
--   x ¦             ¦ q j
--     ¦             ¦
--     x ----------> y
--           p i
--
-- In the drawing the direction i goes left-to-right and j goes
-- bottom-to-top. As we are constructing a path from x to z along i we
-- have i : I in the context already and we put p i as bottom. The
-- direction j that we are doing the composition in is abstracted in
-- the first argument to hcomp.

-- These are related to lifting conditions for Kan cubical sets.

-- A more natural form of composition of paths in Cubical Agda is
-- ternary composition:
--
--          x             w
--          ^             ^
--          ¦             ¦
--  p (~ j) ¦             ¦ r j
--          ¦             ¦
--          y ----------> z
--                q i
--
-- This is written p ∙∙ q ∙∙ r in the agda/cubical library (∙ is "\.")
-- and implemented by:

_∙∙_∙∙_ : {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ∙∙ q ∙∙ r) i = hcomp (λ j → λ { (i = i0) → p (~ j)
                                 ; (i = i1) → r j })
                        (q i)

-- Note that we can easily define mixfix operators with many arguments
-- in Agda.

-- Using this we can define compPath much slicker:
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

-- To prove algebraic properties of this operation (in particular that
-- it's a groupoid) we need to talk about filling. There is no time
-- for this today, but the interested reader can consult
--
--    Cubical.Foundations.GroupoidLaws

-- In case there is time I might show the following briefly:

doubleCompPath-filler : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hfill (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (inS (q i)) j

compPath-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
                → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler p q = doubleCompPath-filler refl p q

rUnit : {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit p i j = compPath-filler p refl i j


-- Having hcomp as a primitive operation lets us prove many things
-- very directly. For instance, we can prove that any proposition is
-- also a set using a higher dimensional hcomp.
isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet h1 h2 i x y = isPropIsProp (h1 x y) (h2 x y) i

