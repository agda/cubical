{-

Cubical Agda - A Dependently Typed PL with Univalence and HITs
==============================================================
                    Anders Mörtberg
       Every Proof Assistant - September 17, 2020


Link to slides: https://staff.math.su.se/anders.mortberg/slides/EPA2020.pdf

Link to video: https://vimeo.com/459020971

-}

-- To make Agda cubical add the --cubical option.
-- This is implicitly added for files in the cubical library via the cubical.agda-lib file.
module Cubical.Talks.EPA2020 where

-- The "Foundations" package contain a lot of important results (in
-- particular the univalence theorem)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int
open import Cubical.Data.Prod.Base


-- The interval in Cubical Agda is written I and the endpoints i0 and i1.

apply0 : (A : Type) (p : I → A) → A
apply0 A p = p i0

-- We omit the universe level ℓ for simplicity in this talk. In the
-- library everything is maximally universe polymorphic.


-- We can write functions out of the interval using λ-abstraction:
refl' : {A : Type} (x : A) → x ≡ x
refl' x = λ i → x
-- In fact, x ≡ y is short for PathP (λ _ → A) x y

refl'' : {A : Type} (x : A) → PathP (λ _ → A) x x
refl'' x = λ _ → x

-- In general PathP A x y has A : I → Type, x : A i0 and y : A i1
-- PathP = Dependent paths (Path over a Path)

-- We cannot pattern-match on interval variables as I is not inductively defined
-- foo : {A : Type} → I → A
-- foo r = {!r!}   -- Try typing C-c C-c

-- cong has a direct proof
cong' : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong' f p i = f (p i)

-- function extensionality also has a direct proof.
-- It also has computational content: swap the arguments.
funExt' : {A B : Type} {f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
funExt' p i x = p x i

-- Transport is more complex as ≡ isn't inductively defined (so we
-- can't define it by pattern-matching on p)
transport' : {A B : Type} → A ≡ B → A → B
transport' p a = transp (λ i → p i) i0 a

-- This lets us define subst (which is called "transport" in the HoTT book)
subst' : {A : Type} (P : A → Type) {x y : A} (p : x ≡ y) → P x → P y
subst' P p pa = transport (λ i → P (p i)) pa

-- The transp operation reduces differently for different types
-- formers. For paths it reduces to another primitive operation called
-- hcomp.

-- We can also define the J eliminator (aka path induction)
J' : {A : Type} {B : A → Type} {x : A}
     (P : (z : A) → x ≡ z → Type)
     (d : P x refl) {y : A} (p : x ≡ y) → P y p
J' P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- So J is provable, but it doesn't satisfy computation rule
-- definitionally. This is almost never a problem in practice as the
-- cubical primitives satisfy many new definitional equalities.



-- Another key concept in HoTT/UF is the Univalence Axiom. In Cubical
-- Agda this is provable, we hence refer to it as the Univalence
-- Theorem.

-- The univalence theorem: equivalences of types give paths of types
ua' : {A B : Type} → A ≃ B → A ≡ B
ua' = ua

-- Any isomorphism of types gives rise to an equivalence
isoToEquiv' : {A B : Type} → Iso A B → A ≃ B
isoToEquiv' = isoToEquiv

-- And hence to a path
isoToPath' : {A B : Type} → Iso A B → A ≡ B
isoToPath' e = ua' (isoToEquiv' e)

-- ua satisfies the following computation rule
-- This suffices to be able to prove the standard formulation of univalence.
uaβ' : {A B : Type} (e : A ≃ B) (x : A)
     → transport (ua' e) x ≡ fst e x
uaβ' e x = transportRefl (equivFun e x)



-- Time for an example!

-- Booleans
data Bool : Type where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false

notPath : Bool ≡ Bool
notPath = isoToPath' (iso not not rem rem)
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem false = refl
  rem true  = refl

_ : transport notPath true ≡ false
_ = refl


-- Another example, integers:

sucPath : ℤ ≡ ℤ
sucPath = isoToPath' (iso sucℤ predℤ sucPred predSuc)

_ : transport sucPath (pos 0) ≡ pos 1
_ = refl

_ : transport (sucPath ∙ sucPath) (pos 0) ≡ pos 2
_ = refl

_ : transport (sym sucPath) (pos 0) ≡ negsuc 0
_ = refl



-----------------------------------------------------------------------------
-- Higher inductive types

-- The following definition of finite multisets is due to Vikraman
-- Choudhury and Marcelo Fiore.

infixr 5 _∷_

data FMSet (A : Type) : Type where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
--  trunc : (xs ys : FMSet A) (p q : xs ≡ ys) → p ≡ q

-- We need to add the trunc constructor for FMSets to be sets, omitted
-- here for simplicity.

_++_ : ∀ {A : Type} (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
-- trunc xs zs p q i j ++ ys =
--   trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitr-++ : {A : Type} (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ [] = refl
unitr-++ (x ∷ xs) = cong (x ∷_) (unitr-++ xs)
unitr-++ (comm x y xs i) j = comm x y (unitr-++ xs j) i
-- unitr-++ (trunc xs ys x y i j) = {!!}


-- This is a special case of set quotients! Very useful for
-- programming and set level mathematics

data _/_ (A : Type) (R : A → A → Type) : Type where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : (a b : A / R) (p q : a ≡ b) → p ≡ q

-- Proving that they are effective ((a b : A) → [ a ] ≡ [ b ] → R a b)
-- requires univalence for propositions.


-------------------------------------------------------------------------
-- Topological examples of things that are not sets

-- We can define the circle as the following simple data declaration:
data S¹ : Type where
  base : S¹
  loop : base ≡ base

-- We can write functions on S¹ using pattern-matching equations:
double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

helix : S¹ → Type
helix base     = ℤ
helix (loop i) = sucPathℤ i

ΩS¹ : Type
ΩS¹ = base ≡ base

winding : ΩS¹ → ℤ
winding p = subst helix p (pos 0)

_ : winding (λ i → double ((loop ∙ loop) i)) ≡ pos 4
_ = refl


-- We can define the Torus as:
data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

-- And prove that it is equivalent to two circle:
t2c : Torus → S¹ × S¹
t2c point        = (base , base)
t2c (line1 i)    = (loop i , base)
t2c (line2 j)    = (base , loop j)
t2c (square i j) = (loop i , loop j)

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl

-- Using univalence we get the following equality:
Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath' (iso t2c c2t t2c-c2t c2t-t2c)


windingTorus : point ≡ point → ℤ × ℤ
windingTorus l = ( winding (λ i → proj₁ (t2c (l i)))
                 , winding (λ i → proj₂ (t2c (l i))))

_ : windingTorus (line1 ∙ sym line2) ≡ (pos 1 , negsuc 0)
_ = refl

-- We have many more topological examples, including Klein bottle, RP^n,
-- higher spheres, suspensions, join, wedges, smash product:
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.RPn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

-- There's also a proof of the "3x3 lemma" for pushouts in less than
-- 200LOC. In HoTT-Agda this took about 3000LOC. For details see:
-- https://github.com/HoTT/HoTT-Agda/tree/master/theorems/homotopy/3x3
open import Cubical.HITs.Pushout

-- We also defined the Hopf fibration and proved that its total space
-- is S³ in about 300LOC:
open import Cubical.Homotopy.Hopf
open S¹Hopf

-- There is also some integer cohomology in Cubical.ZCohomology.
-- To compute cohomology groups of various spaces we need a bunch of
-- interesting theorems: Freudenthal suspension theorem,
-- Mayer-Vietoris sequence...
open import Cubical.Homotopy.Freudenthal
open import Cubical.ZCohomology.MayerVietorisUnreduced


-------------------------------------------------------------------------
-- The structure identity principle

-- A more efficient version of finite multisets based on association lists
open import Cubical.HITs.AssocList.Base

-- data AssocList (A : Type) : Type where
--  ⟨⟩ : AssocList A
--  ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
--  per : (a b : A) (m n : ℕ) (xs : AssocList A)
--      → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
--  agg : (a : A) (m n : ℕ) (xs : AssocList A)
--      → ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs ≡ ⟨ a , m + n ⟩∷ xs
--  del : (a : A) (xs : AssocList A) → ⟨ a , 0 ⟩∷ xs ≡ xs
--  trunc : (xs ys : AssocList A) (p q : xs ≡ ys) → p ≡ q


-- Programming and proving is more complicated with AssocList compared
-- to FMSet. This kind of example occurs everywhere in programming and
-- mathematics: one representation is easier to work with, but not
-- efficient, while another is efficient but difficult to work with.

-- Solution: substitute using univalence
substIso : {A B : Type} (P : Type → Type) (e : Iso A B) → P A → P B
substIso P e = subst P (isoToPath e)

-- Can transport for example Monoid structure from FMSet to AssocList
-- this way, but the achieved Monoid structure is not very efficient
-- to work with. A better solution is to prove that FMSet and
-- AssocList are equal *as monoids*, but how to do this?

-- Solution: structure identity principle (SIP)
-- This is a very useful consequence of univalence
open import Cubical.Foundations.SIP

sip' : {ℓ : Level} {S : Type ℓ → Type ℓ} {ι : StrEquiv S ℓ}
       (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ S) → A ≃[ ι ] B → A ≡ B
sip' = sip

-- The tricky thing is to prove that (S,ι) is a univalent structure.
-- Luckily we provide automation for this in the library, see for example:
open import Cubical.Algebra.Monoid.Base

-- Another cool application of the SIP: matrices represented as
-- functions out of pairs of Fin's and vectors are equal as abelian
-- groups:
open import Cubical.Algebra.Matrix


-- The end, back to slides!
