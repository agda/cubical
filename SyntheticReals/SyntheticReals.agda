{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.SyntheticReals where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Structures.Poset
open import Cubical.Foundations.Function

open import Function.Base using (_∋_)
-- open import Function.Reasoning using (∋-syntax)
open import Function.Base using (it) -- instance search

open import Utils
open import MoreLogic
open MoreLogic.Reasoning
open MoreLogic.Properties
open import MoreAlgebra
open MoreAlgebra.Definitions
open MoreAlgebra.Consequences
open import Bundles
-- open MoreAlgebra.Properties.Group

-- https://www.cs.bham.ac.uk/~abb538/thesis.pdf
-- Booij 2020 - Analysis in Univalent Type Theory

-- Lemma 4.1.6.
import Properties.ConstructiveField

-- Lemma 4.1.11.
import Properties.AlmostOrderedField

-- Lemma 4.1.12. An ordered field (F, 0, 1, +, · , min, max, <) is a constructive field (F, 0, 1, +, · , #).
lemma-4-1-12 :
  -- NOTE: we do a slightly different thing here
  ∀{ℓ ℓ'} (OF : OrderedField {ℓ} {ℓ'}) →
  let open OrderedField OF
  ----------------------------------------------------
  in (IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ)
lemma-4-1-12 {ℓ} {ℓ'} OF = let -- NOTE: for mentioning the ℓ and ℓ' and not taking them as new "variables" we bring them into scope
  open OrderedField OF
  in record -- We need to show that + is #-extensional, and that # is tight.
   { OrderedField OF
   ; isApartnessRel  = #'-isApartnessRel <-isStrictPartialOrder -- NOTE: We've proved this before

     -- First, assume w + x # y + z. We need to show w # y ∨ x # z.
   ; +-#-extensional = λ where
                       -- Consider the case w + x < y + z, so that we can use (†) to obtain w < y ∨ x < z,
                       --   which gives w # y ∨ x # z in either case.
                       w x y z (inl w+x<y+z) → case +-<-extensional _ _ _ _ w+x<y+z of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ -- NOTE: here we had to add a (return-)type annotation to the λ
                         { (inl w<y) → inl (inl w<y)
                         ; (inr x<z) → inr (inl x<z)
                         })
                       -- The case w + x > y + z is similar.
                       w x y z (inr y+z<w+x) → case  +-<-extensional _ _ _ _ y+z<w+x of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ
                         { (inl y<w) → inl (inr y<w)
                         ; (inr z<x) → inr (inr z<x)
                         })

     -- Tightness follows from the fact that ≤ is antisymmetric, combined with the fact
     --   that ¬(P ∨ Q) is equivalent to ¬P ∧ ¬Q.
   ; #-tight         = λ x y ¬[x<y]⊎¬[y<x] → let (¬[x<y] , ¬[y<x]) = deMorgan₂' ¬[x<y]⊎¬[y<x]
                                             in  ≤-antisym _ _ ¬[y<x] ¬[x<y]
   }

-- We will mainly be concerned with ordered fields, as opposed to the more general con-
-- structive fields. This is because the Archimedean property can be phrased straightforwardly
-- for ordered fields, as in Section 4.3, and because the ordering relation allows us to define loca-
-- tors, as in Chapter 6.
--
-- We have defined ordered fields, which capture the algebraic structure of the real numbers.

-- 4.2 Rationals
-- ...
-- NOTE: we have in cubical
--   import Cubical.HITs.Rationals.HITQ
--     ℚ as a higher inductive type
--   import Cubical.HITs.Rationals.QuoQ
--     ℚ as a set quotient of ℤ × ℕ₊₁ (as in the HoTT book)
--   import Cubical.HITs.Rationals.SigmaQ
--     ℚ as the set of coprime pairs in ℤ × ℕ₊₁

import Cubical.HITs.Rationals.QuoQ renaming (ℚ to ℚ-Carrier)

postulate
  ℚℓ : Level
  ℚOF : OrderedField {ℓ-zero} {ℚℓ}
{-
ℚ = λ where
  .OrderedField.Carrier        → ℚ-Carrier
  .OrderedField.0f             → 0
  .OrderedField.1f             → 1
  .OrderedField._+_            → _+_
  .OrderedField.-_             → -_
  .OrderedField._·_            → _*_
  .OrderedField.min            → {!!}
  .OrderedField.max            → {!!}
  .OrderedField._<_            → {!!}
  .OrderedField.<-isProp       → {!!}
  .OrderedField._⁻¹ᶠ           → {!!}
  .OrderedField.isOrderedField → {!!}
-}

-- 4.3 Archimedean property
--
-- We now define the notion of Archimedean ordered fields. We phrase this in terms of a certain
-- interpolation property, that can be defined from the fact that there is a unique morphism of
-- ordered fields from the rationals to every ordered field.

-- Lemma 4.3.3. For every ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ), there is a unique morphism
-- i of ordered fields from the rationals to F . Additionally, i preserves < in the sense that for every q, r : Q
--   q < r ⇒ i (q) < F i (r ).

-- ∃! : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
-- ∃! A B = isContr (Σ A B)

-- isContr' A = Σ[ x ∈ A ] (∀ y → x ≡ y)

ℚ-IsInitialObject : ∀(OF : OrderedField {ℓ} {ℓ'}) → isContr (OrderedFieldMor ℚOF OF)
ℚ-IsInitialObject OF = {!!} , {!!}

-- Definition 4.3.5. Let (F, 0 F , 1 F , + F , · F , min F , max F , < F ) be an ordered field, so that we get a
-- canonical morphism i : Q → F of ordered fields, as in Lemma 4.3.3. We say the ordered field
-- (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is Archimedean if
--   (∀x, y : F )(∃q : Q)x < i (q) < y.

IsArchimedian : OrderedField {ℓ} {ℓ'} → Type (ℓ-max ℓ ℓ')
IsArchimedian OF = let (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
                       open OrderedField OF
                       ℚ = OrderedField.Carrier ℚOF
                   in ∀ x y → ∃[ q ∈ ℚ ] (x < i q) × (i q < y)

-- If the ordered field is clear from the context, we will identify rationals q : Q with their in-
-- clusion i (q) in the ordered field, so that we may also say that (F, 0 F , 1 F , + F , · F , min F , max F , < F )
-- is Archimedean if
-- (∀x, y : F )(∃q : Q)x < q < y.

-- Example 4.3.6. In an Archimedean ordered field, all numbers are bounded by rationals. That
-- is, for a given x : F , there exist q, r : Q with q < x < r .

Example-4-3-6 : (OF : OrderedField {ℓ} {ℓ'})
              → IsArchimedian OF
              → let open OrderedField OF renaming (Carrier to F)
                    (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
                    ℚ = OrderedField.Carrier ℚOF
                in ∀(x : F) → (∃[ q ∈ ℚ ] i q < x) × (∃[ r ∈ ℚ ] x < i r)
-- This follows from applying the Archimedean property to x − 1 < x and x < x + 1.
Example-4-3-6 OF isArchimedian = {!!}

-- 4.4 Cauchy completeness of real numbers
--
-- We focus on Cauchy completeness, rather than Dedekind or Dedekind-MacNeille completeness,
-- as we will focus on the computation of digit expansions, for which Cauchy completeness suffices.

-- In order to state that an ordered field is Cauchy complete, we need to define when sequences
-- are Cauchy, and when a sequence has a limit. We also take the opportunity to define
-- the set of Cauchy reals in Definition 4.4.9. Surprisingly, this ordered field cannot be shown to
-- be Cauchy complete.

-- NOTE: in the following we make use of ℚ⁺ a few times. Maybe this should be a primitive?

-- Fix an ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ).
module _ (OF : OrderedField {ℓ} {ℓ'}) where
  open OrderedField OF renaming (Carrier to F)
  -- module ℚ = OrderedField ℚ
  open OrderedField ℚOF using () renaming (_<_ to _<ᵣ_; 0f to 0ᵣ)
  ℚ = OrderedField.Carrier ℚOF
  iᵣ = OrderedFieldMor.fun (fst (ℚ-IsInitialObject OF))
  open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)

  -- We get a notion of distance, given by the absolute value as
  --   |x − y| := max F (x − y, −(x − y)).

  distance : ∀(x y : F) → F
  distance x y = max (x - y) (- (x - y))

  -- Consider a sequence x : N → F of elements of F . Classically, we may state that x is Cauchy as
  -- (∀ε : Q + )(∃N : N)(∀m, n : N)m, n ≥ N ⇒ |x m − x n | < ε,
  IsCauchy : (x : ℕ → F) → Type (ℓ-max ℓ' ℚℓ)
  IsCauchy x = ∀(ε : ℚ) → 0ᵣ <ᵣ ε → ∃[ N ∈ ℕ ] ∀(m n : ℕ) → N ≤ₙ m → N ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- We can interpret the quantifiers as in Definition 2.4.5.
  -- NOTE: this is the case, since `∃ A B = ∥ Σ A B ∥`

  -- Following a propositions-as-types interpretation, we may also state that x is Cauchy as the
  -- structure
  -- (Πε : Q + )(ΣN : N)(Πm, n : N)m, n ≥ N → |x m − x n | < ε.

  -- The dependent sum represents a choice of index N for every error ε, and so we have arrived at the following definition.

  -- Definition 4.4.1.
  -- For a sequence of reals x : N → F , a a modulus of Cauchy convergence is a map M : Q + → N such that
  -- (∀ε : Q + )(∀m, n : N)m, n ≥ M (ε) ⇒ |x m − x n | < ε.

  -- NOTE: do we already call these x "reals" ?
  -- NOTE: we are using the Modulus-type `((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)` a few times and might abbreviate it

  IsModulusOfCauchyConvergence : (x : ℕ → F) → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)) → Type (ℓ-max ℓ' ℚℓ)
  IsModulusOfCauchyConvergence x M = ∀(ε : ℚ) → (p : 0ᵣ <ᵣ ε) → ∀(m n : ℕ)
                                   → let instance _ = p
                                     in M ε ≤ₙ m → M ε ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- In constructive mathematics, we typically use such sequences with modulus, for example,
  -- because they can sometimes be used to compute limits of Cauchy sequences, avoiding choice axioms.

  -- Definition 4.4.2.
  -- A number l : F is the limit of a sequence x : N → F if the sequence
  -- converges to l in the usual sense:
  --   (∀ε : Q + )(∃N : N)(∀n : N)n ≥ N ⇒ |x n − l | < ε.

  IsLimit : (x : ℕ → F) → (l : F) → Type (ℓ-max ℓ' ℚℓ)
  IsLimit x l = ∀(ε : ℚ) → (0ᵣ <ᵣ ε) → ∃[ N ∈ ℕ ] ∀(n : ℕ) → N ≤ₙ n → distance (x n) l < iᵣ ε

  -- Remark 4.4.3. We do not consider the statement of convergence in propositions-as-types
  --
  --   (Πε : Q + )(ΣN : N)(Πn : N)n ≥ N → |x n − l | < ε,
  --
  -- because if the sequence has a modulus of Cauchy convergence M, then λε.M (ε/2) is a
  -- modulus of convergence to the limit l, so that we get an element of the above type.

  -- Definition 4.4.4.
  -- The ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is said to be Cauchy complete
  -- if for every sequence x with modulus of Cauchy convergence M, we have a limit of x.
  -- In other words, an ordered field is Cauchy complete iff from a sequence–modulus pair (x, M), we can compute a limit of x.

  IsCauchyComplete : Type (ℓ-max (ℓ-max ℓ ℓ') ℚℓ)
  IsCauchyComplete = (x : ℕ → F)
                   → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                   → IsModulusOfCauchyConvergence x M
                   → Σ[ l ∈ F ] IsLimit x l

  -- For the remainder of this section, additionally assume that F is Archimedean.
  module _ (isArchimedian : IsArchimedian OF) where

    -- Lemma 4.4.5.
    -- The type of limits of a fixed sequence x : N → F is a proposition.
    Lemma-4-4-5 : ∀(x : ℕ → F) → isProp (Σ[ l ∈ F ] IsLimit x l)
    -- Proof. This can be shown using the usual proof that limits are unique in Archimedean ordered fields, followed by an application of Lemma 2.6.20.
    Lemma-4-4-5 x = {!!}

    -- Corollary 4.4.6.
    -- Fix a given sequence x : N → F . Suppose that we know that there exists a
    -- limit of the sequence. Then we can compute a limit of the sequence.
    Corollary-4-4-6 : ∀(x : ℕ → F) → (∃[ l ∈ F ] IsLimit x l) → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-6 x p = {!!} , {!!}

    -- Corollary 4.4.7.
    -- Fix a given sequence x : N → F . Suppose that, from a modulus of Cauchy
    -- convergence, we can compute a limit of the sequence. Then from the existence of the modulus of
    -- Cauchy convergence we can compute a limit of the sequence.
    Corollary-4-4-7 : (x : ℕ → F)
                    → ( (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                      → (isMCC : IsModulusOfCauchyConvergence x M)
                      → Σ[ l ∈ F ] IsLimit x l
                      )
                    -----------------------------------------------------------------------
                    → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence x M
                    → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-7 x f p = {!!}

    -- We can thus compute the limit of x : N → F as the number lim(x, p), where p is a proof
    -- that the limit of x exists. We will rather use the more traditional notation lim n→∞ x n for this
    -- number.

    -- Example 4.4.8 (Exponential function).
    -- In a Cauchy complete Archimedean ordered field, we can define an exponential function exp : F → F by
    --
    --    exp(x) = Σ_{k=0}^{∞} (xᵏ) / (k!)
    --
    -- For a given input x, we obtain the existence of a modulus of Cauchy convergence for the output from boundedness of
    -- x, that is, from the fact that (∃q, r : Q) q < x < r .

    exp : F → F
    exp x = {!!}

    Example-4-4-8 : ∀(x : F) → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence {!!} M
    Example-4-4-8 x with Example-4-3-6 OF isArchimedian x
    ... | q' , r' = let q : ∃[ q ∈ ℚ ] iᵣ q < x
                        q = q'
                        r : ∃[ r ∈ ℚ ] x < iᵣ r
                        r = r'
                    in {!!}

    -- The point of this work is that, because we have a single language for properties and struc-
    -- ture, we can see more precisely what is needed for certain computations. In the above example,
    -- we explicitly do not require that inputs come equipped with a modulus of Cauchy convergence,
    -- but rather that there exists such a modulus. On the one hand, we do need a modulus to obtain
    -- the limit, but as the limit value is independent of the chosen modulus, existence of such a
    -- modulus suffices.

    -- Definition 4.4.9. The Cauchy reals ℝC is the collection of rational sequences equipped with
    -- a modulus of Cauchy convergence, quotiented (as in Section 2.7) by an equivalence relation
    -- that relates two sequence–modulus pairs (x, M) and (y, N ) iff
    -- (∀ε : Q + ) x M (ε/4) − y M (ε/4) < ε.

    ℝC : {!!}
    ℝC = {!!}

    -- The Cauchy reals form an Archimedean ordered field in a natural way. The natural strategy
    -- to prove that the Cauchy reals are Cauchy complete, perhaps surprisingly, does not work, and
    -- in some constructive foundations the Cauchy completeness of the Cauchy reals is known to
    -- be false [68].
    --
    -- ...
    --
    -- An alternative interpretation of the non-completeness of the Cauchy reals is that the sequential
    -- definition of completeness ought to be amended [80].

    -- NOTE: now we're back to https://github.com/agda/cubical/issues/286 ?


-- Auke would send an email to Ayberk Tosun and Martin Escardo
-- I could prepare a PR for the cubical standard library
-- the cubical standard library does not supersede the standard library
--   using setoids need not to be a shortcoming but can be a concious decision
-- Postulating the rationals as an ordered field for which there exists a unique morphism to every other ordered field should be sufficient
--   (we went a little bit into the coprime and quotient construction of the rational numbers)
-- I can prepare some statements that I would like to formalize (with just guessing) to have a more concrete guidance for the necessary detail of a real number formulation
-- the impredicative `--prop` is not equivalent to hProp
--   therefore, one should make props explicit arguments or at least be aware of them at all times


{-

in a world where we "just have" real numbers in Agda, I would do the following:

Adjoint theory
  Vector space
  normed space
  Banach space
  Inner Product space
  unbounded Linear operator
  adjoint linear operator
  orthogonal decomposition of Banach spaces
  inf-sup conditions
  lax-milgram

Local Multilinear Algebra
  euclidean space
  linear representation of hodge star
  locally euclidean

Global Multilinear Algebra
  locally euclidean topological space
  chart representation


-}
