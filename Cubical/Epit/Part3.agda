{-
Part 3: Univalence and the SIP
• Univalence from ua and uaβ
• Transporting with ua
• Subst using ua
• The SIP as a consequence of ua
• Examples of using the SIP for math and programming (algebra, data
  structures, etc.)
-}

{-# OPTIONS --cubical #-}
module Cubical.Epit.Part3 where

open import Cubical.Core.Glue public
  using ( Glue ; glue ; unglue ; lineToEquiv )

open import Cubical.Foundations.Prelude hiding (refl ; transport ; subst ; sym ; transportRefl ; _∙_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Epit.Part2 public


-- A key concept in HoTT/UF is univalence. As we have seen earlier in
-- the week this is assumed as an axiom. In Cubical Agda it is instead
-- provable and hence has computational content. This means that
-- transporting with paths constructed using univalence reduces as
-- opposed to HoTT where they would be stuck. This simplifies some
-- proofs and make it possible to actually do concrete computations
-- using univalence.

-- The part of univalence which is most useful for our applications is
-- to be able to turn equivalences (written _≃_ and defined as Σ-type
-- of a function and a proof that it has contractible fibers) into
-- paths:
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })
-- This term is defined using "Glue types". We won't have time to go
-- into details about them today, but for practical applications one
-- can usually forget about them and use ua as a black box.

-- The important point is that transporting along the path constructed
-- using ua applies the function underlying the equivalence. This is
-- easily proved using transportRefl:
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ fst e x
uaβ e x = transportRefl (equivFun e x)

-- The fact that we have both ua and uaβ suffices to be able to prove
-- the standard formulation of univalence. For details see:
--
-- open import Cubical.Foundations.Univalence

-- The standard way of constructing equivalences is to start with an
-- isomorphism and then improve it into an equivalence. The lemma in
-- the library which does this is
--
-- isoToEquiv : {A B : Type ℓ} → Iso A B → A ≃ B

-- Composing this with ua gives us a way to turn isomorphisms into paths:
--
-- isoToPath : {A B : Type ℓ} → Iso A B → A ≡ B



-- Time for an example!

-- Booleans
data Bool : Type₀ where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false

notPath : Bool ≡ Bool
notPath = isoToPath (iso not not rem rem)
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem false = refl
  rem true  = refl

_ : transport notPath true ≡ false
_ = refl


-- Another example, integers:

open import Cubical.Data.Int hiding (_+_ ; +-assoc)

sucPath : Int ≡ Int
sucPath = isoToPath (iso sucInt predInt sucPred predSuc)

_ : transport sucPath (pos 0) ≡ pos 1
_ = refl

_ : transport (sucPath ∙ sucPath) (pos 0) ≡ pos 2
_ = refl

_ : transport (sym sucPath) (pos 0) ≡ negsuc 0
_ = refl


-------------------------------------------------------------------------
-- The structure identity principle

substEquiv : (S : Type ℓ → Type ℓ') (e : A ≃ B) → S A → S B
substEquiv S e = subst S (ua e)

-- This lets us transport any structure on A to get a structure on
-- B. Example with binary numbers:

-- Warning: the following doesn't work with development version?
open import Cubical.Data.BinNat.BinNat renaming (ℕ≃binnat to ℕ≃Bin ; binnat to Bin)

open import Cubical.Data.Nat

T : Set → Set
T X = Σ[ _+_ ∈ (X → X → X) ] ((x y z : X) → x + (y + z) ≡ (x + y) + z)

TBin : T Bin
TBin = substEquiv T ℕ≃Bin (_+_ , +-assoc)

_+Bin_ : Bin → Bin → Bin
_+Bin_  = fst TBin

+Bin-assoc : (m n o : Bin) → m +Bin (n +Bin o) ≡ (m +Bin n) +Bin o
+Bin-assoc = snd TBin


-- This is however not always what we want was _+Bin_ will translate
-- its input to unary numbers, add, and then translate back. Instead
-- we want to use efficient addition on binary numbers, but get the
-- associativity proof for free. For details see Section 2.1.1 of:
--
-- https://www.doi.org/10.1017/S0956796821000034
-- (Can be downloaded from: https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf)


-- Another paper which discusses similar things with many more examples is:
--
-- Internalizing Representation Independence with Univalence
-- Carlo Angiuli, Evan Cavallo, Anders Mörtberg, Max Zeuner
-- https://arxiv.org/abs/2009.05547
