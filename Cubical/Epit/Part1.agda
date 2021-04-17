{-# OPTIONS --cubical #-}
module Cubical.Epit.Part1 where

-- To load an Agda file type "C-c C-l" in emacs (the notation "C-c"
-- means that one should hold "CTRL" and press "c", for general
-- documentation about emacs keybindings see:
-- https://www.gnu.org/software/emacs/manual/html_node/efaq/Basic-keys.html)

-- The "Core" package of the agda/cubical library sets things for us
-- open import Cubical.Foundations.Everything
-- The "Foundations" package of agda/cubical contains a lot of
-- important results (in particular the univalence theorem). As we
-- will develop many things from scratch we don't import it here, but
-- a typical file in the library would import the relevant files from
-- Foundations which it uses. To get everything in Foundations write:
--
-- open import Cubical.Foundations.Everything hiding (id ; refl)

-- To search for something among the imported files press C-s C-z and
-- then write what you want to search for.

-- Documentation of the Cubical Agda mode can be found at:
-- https://agda.readthedocs.io/en/v2.6.1.3/language/cubical.html

open import Cubical.Core.Primitives public

------------------------------------------------------------------------------
--                             Agda Basic                                   --
------------------------------------------------------------------------------

-- We parametrize everything by some universe levels (as opposed to
-- Coq we always have to give these explicitly unless we work with the
-- lowest universe)
variable
  ℓ ℓ' ℓ'' : Level

-- Universes in Agda are called "Set", but in order to avoid confusion
-- with h-sets we rename them to "Type".

-- Functions in Agda are written using equations:
id : {A : Type ℓ} → A → A
id x = x
-- The {A : Type} notation says that A is an implicit argument of Type ℓ.

-- The notation (x : A) → B and {x : A} → B introduces a dependent
-- function (so B might mention B), in other words an element of a
-- Π-type.

-- We could also write this using a λ-abstraction:
id' : {A : Type ℓ} → A → A
id' = λ x → x
-- To input a nice symbol for the lambda write "\lambda". Agda support
-- Unicode symbols natively:
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input
-- To input the "ℓ" write "\ell"

-- We can build Agda terms interactively in emacs by writing a ? as RHS:
--
-- id'' : {A : Type ℓ} → A → A
-- id'' = ?
--
-- Try uncommenting this and pressing "C-c C-l". This will give us a
-- hole and by entering it with the cursor we can get information
-- about what Agda expects us to provide and get help from Agda in
-- providing this.
--
-- By pressing "C-c C-," while having the cursor in the goal Agda
-- shows us the current context and goal. As we're trying to write a
-- function we can press "C-c C-r" (for refine) to have Agda write the
-- λ-abstraction "λ x → ?" automatically for us. If one presses "C-c C-,"
-- in the hole again "x : A" will now be in the context. If we type
-- "x" in the hole and press "C-c C-." Agda will show us that we have
-- an A, which is exactly what we want to provide to fill the goal. By
-- pressing "C-c C-SPACE" Agda will then fill the hole with "x" for us.
--
-- Agda has lots of handy commands like this for manipulating goals:
-- https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#commands-in-context-of-a-goal

-- A good resource to get start with Agda is the documentation:
-- https://agda.readthedocs.io/en/latest/getting-started/index.html





------------------------------------------------------------------------------
--                     The interval and path types                          --
------------------------------------------------------------------------------


-- The interval in Cubical Agda is written I and the endpoints are
--
--   i0 : I
--   i1 : I
--
-- These stand for "interval 0" and "interval 1".

-- We can apply a function out of the interval to an endpoint just
-- like we would apply any Agda function:
apply0 : (A : Type ℓ) (p : I → A) → A
apply0 A p = p i0

-- The equality type _≡_ is not inductively defined in Cubical Agda,
-- instead it's a builtin primitive. An element of x ≡ y consists of a
-- function p : I → A such that p i0 is definitionally x and p i1 is
-- definitionally y. The check that the endpoints are correct when we
-- provide a p : I → A is automatically checked by Agda during
-- typechecking, so introducing an element of x ≡ y is done just like
-- how we introduce elements of I → A but Agda will check the side
-- conditions.
--
-- So we can write paths using λ-abstraction:
path1 : {A : Type ℓ} (x : A) → x ≡ x
path1 x = λ i → x
--
-- As explained above Agda checks that whatever we write as definition
-- matches the path that we have written (so the endpoints have to be
-- correct). In this case everything is fine and path1 can be thought
-- of as a proof reflexivity. Let's give it a nicer name and more
-- implicit arguments:
--
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ i → x
--
-- The notation {x = x} lets us access the implicit argument x (the x
-- in the LHS) and rename it to x (the x in the RHS) in the body of refl.
-- We could just as well have written:
--
-- refl : {A : Type ℓ} {x : A} → x ≡ x
-- refl {x = y} = λ i → y


-- Note that we cannot pattern-match on interval variables as I is not
-- inductively defined:
--
-- foo : {A : Type} → I → A
-- foo r = {!r!}   -- Try typing C-c C-c


-- It often gets tiring to write {A : Type ℓ} everywhere, so let's
-- assume that we have some types:
variable
  A B : Type ℓ
-- This will make A and B elements of different universes (all
-- arguments is maximally generalized) and all definitions that use
-- them will have them as implicit arguments.

-- We can now implement some basic operations on _≡_. Let's start with
-- cong (called "ap" in the HoTT book):
cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f p i = f (p i)

-- Note that the definition differs from the HoTT definition in that
-- it is not defined by J or pattern-matching on p, but rather it's
-- just a direct definition as a composition fo functions. Agda treats
-- p : x ≡ y as a function, so we can just apply it to i to get an
-- element of A which at i0 is x and at i1 is y. By applying f to this
-- element we hence get an element of B which at i0 is f x and at i1
-- is f y.

-- As this is just function composition it satisfies lots of nice
-- definitional equalities, see the Warmup.agda file. Some of these
-- are not satisfied by the HoTT definition of cong/ap.

-- In HoTT function extensionality is proved as a consequence of
-- univalence using a rather ingenious proof due to Voevodsky, but in
-- cubical systems it has a much more direct proof. As paths are just
-- functions we can get it by just swapping the arguments to p:
funExt : {f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

-- To see that this has the correct type not that when i is i0 we have
-- "p x i0 = f x" and when i is i1 we have "p x i1 = g x", so by η for
-- functions we have a path f ≡ g as desired.



-- The interval has additional operations:
--
-- Minimum: _∧_ : I → I → I
-- Maximum: _∨_ : I → I → I
-- Symmetry: ~_ : I → I
--
-- Agda remark: the _ indicate where arguments should go.
--
-- These satisfy the equations of a De Morgan algebra (i.e. a
-- distributive lattice (_∧_ , _∨_ , i0 , i1) with an involution
-- ~). So we have the following kinds of equations definitionally:
--
-- i0 ∨ i    = i
-- i  ∨ i1   = i1
-- i  ∨ j    = j ∨ i
-- i0 ∧ i    = i0
-- i1 ∧ i    = i
-- i  ∧ j    = j ∧ i
-- ~ (~ i)   = i
-- i0        = ~ i1
-- ~ (i ∨ j) = ~ i ∧ ~ j
-- ~ (i ∧ j) = ~ i ∨ ~ j

-- These operations are very useful as they let us define even more
-- things directly. For example symmetry of paths is easily defined
-- using ~:
sym : {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

-- The operations _∧_ and _∨_ are called "connections" and lets us
-- build higher dimensional cubes from lower dimensional ones, for
-- example if we have a path p : x ≡ y then
--
--   sq i j = p (i ∧ j)
--
-- is a square (as we've parametrized by i and j) with the following
-- boundary:
--
--    sq i0 j = p (i0 ∧ j) = p i0 = x
--    sq i1 j = p (i1 ∧ j) = p j
--    sq i i0 = p (i ∧ i0) = p i0 = x
--    sq i i1 = p (i ∧ i1) = p i
--
-- So if we draw this we get:
--
--              p
--        x --------> y
--        ^           ^
--        ¦           ¦
--   refl ¦     sq    ¦ p
--        ¦           ¦
--        ¦           ¦
--        x --------> x
--            refl
--
-- These operations are very useful, for example let's prove that
-- singletons are contractible (aka based path induction).
--
-- We first need the notion of contractible types. For this we need
-- to use a Σ-type:
isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] ((y : A) → x ≡ y)

-- Σ-types are introduced in the file Agda.Builtin.Sigma as the record
-- (modulo some renaming):
--
-- record Σ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
--   constructor _,_
--   field
--     fst : A
--     snd : B fst
--
-- So the projections are fst/snd and the constructor is _,_. We
-- also define non-dependent product as a special case of Σ-types in
-- Cubical.Data.Sigma.Base as:
--
-- _×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
-- A × B = Σ A (λ _ → B)
--
-- The notation ∀ {ℓ ℓ'} lets us omit the type of ℓ and ℓ' in the
-- definition.

-- We define the type of singletons as follows
singl : {A : Type ℓ} (a : A) → Type ℓ
singl {A = A} a = Σ[ x ∈ A ] a ≡ x

-- To show that this type is contractible we need to provide a center
-- of contraction and the fact that any element of it is path-equal to
-- the center
isContrSingl : (x : A) → isContr (singl x)
isContrSingl x = ctr , prf
  where
  -- The center is just a pair with x and refl
  ctr : singl x
  ctr = x , refl

  -- We then need to prove that ctr is equal to any element s : singl x.
  -- This is an equality in a Σ-type, so the first component is a path
  -- and the second is a path over the path we pick as first argument,
  -- so the second component is a square. In fact, we need a square
  -- relating refl and pax, so we can use an _∧_ connection.
  prf : (s : singl x) → ctr ≡ s
  prf (y , pax) i = (pax i) , λ j → pax (i ∧ j)

  -- Agda tip: in order to automatically destruct an argument
  -- (like (y , pax) in prf) write it in the hole and type
  -- C-c C-c. Agda might pick silly names, but it's still very
  -- convenient.

-- As we saw in the second component of prf we often need squares when
-- proving things. In fact, pax (i ∧ j) is a path relating refl to pax
-- *over* another path "λ j → x ≡ pax j". This notion of path over a
-- path is very useful when working in HoTT as well as cubically. In
-- HoTT these are called path-overs and are defined using transport,
-- but in Cubical Agda they are a primitive notion called PathP ("Path
-- of a Path"). In general PathP A x y has
--
--    A : I → Type ℓ
--    x : A i0
--    y : A i1
--
-- So PathP lets us natively define heteorgeneous paths, i.e. paths
-- where the endpoints lie in different types. This lets us specify
-- the type of the second component of prf:
prf' : (x : A) (s : singl x) → (x , refl) ≡ s
prf' x (y , pax) i = (pax i) , λ j → goal i j
  where
  goal : PathP (λ j → x ≡ pax j) refl pax
  goal i j = pax (i ∧ j)


-- Just like _×_ is a special case of Σ-types we have that _≡_ is a
-- special case of PathP. In fact, x ≡ y is just short for PathP (λ _ → A) x y:
reflP : {x : A} → PathP (λ _ → A) x x
reflP {x = x} = λ _ → x


-- Having the primitive notion of equality be heterogeneous is an
-- easily overlooked, but very important, strength of cubical type
-- theory. This allows us to work directly with equality in Σ-types
-- without using transport:
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ[ p ∈ fst x ≡ fst y ] PathP (λ i → B (p i)) (snd x) (snd y)
         → x ≡ y
  ΣPathP eq i = fst eq i , snd eq i

  PathPΣ : x ≡ y
         → Σ[ p ∈ fst x ≡ fst y ] PathP (λ i → B (p i)) (snd x) (snd y)
  PathPΣ eq = (λ i → fst (eq i)) , (λ i → snd (eq i))

  -- The fact that these cancel is proved by refl

-- If one looks carefully the proof of prf uses ΣPathP inlined, in
-- fact this is used all over the place when working cubically and
-- simplifies many proofs which in HoTT requires long complicated
-- reasoning about transport.
isContrΠ : {B : A → Type ℓ'} (h : (x : A) → isContr (B x))
         → isContr ((x : A) → B x)
isContrΠ h = (λ x → fst (h x)) , (λ f i x → snd (h x) (f x) i)

-- Let us end this session with defining propositions and sets
isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

-- In the agda/cubical library we call these h-levels following
-- Voevodsky instead of n-types and index by natural numbers instead
-- of ℕ₋₂. So isContr is h-level 0, isProp is h-level 1, isSet is
-- h-level 2, etc. For details see Cubical/Foundations/HLevels.agda
