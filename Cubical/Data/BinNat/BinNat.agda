{- Binary natural numbers (Anders Mörtberg, Jan. 2019)

This file defines two representations of binary numbers. We prove that
they are equivalent to unary numbers and univalence is then used to
transport both programs and properties between the representations.
This is an example of how having computational univalence can be
useful for practical programming.

The first definition is [Binℕ] and the numbers are essentially lists
of 0/1 with no trailing zeroes (in little-endian format). The main
definitions and examples are:

- Equivalence between Binℕ and ℕ ([Binℕ≃ℕ]) with an equality obtained
  using univalence ([Binℕ≡ℕ]).

- Addition on Binℕ defined by transporting addition on ℕ to Binℕ
  ([_+Binℕ_]) along Binℕ≡ℕ together with a proof that addition on Binℕ
  is associative obtained by transporting the proof for ℕ ([+Binℕ-assoc]).

- Functions testing whether a binary number is odd or even in O(1)
  ([oddBinℕ], [evenBinℕ]) and the corresponding functions for ℕ
  obtained by transport. Proof that odd numbers are not even
  transported from Binℕ to ℕ ([oddℕnotEvenℕ]).

- An example of the structure identity principle for natural number
  structures ([NatImpl]). We first prove that Binℕ≡ℕ lifts to natural
  number structures ([NatImplℕ≡Binℕ]) and we then use this to
  transport "+-suc : m + suc n ≡ suc (m + n)" from ℕ to Binℕ ([+Binℕ-suc]).

- An example of program/data refinement using the structure identity
  principle where we transport a property that is infeasible to prove
  by computation for ℕ ([propDoubleℕ]):

      2^20 * 2^10 = 2^5 * (2^15 * 2^10)

  from the corresponding result on Binℕ which is proved instantly by
  refl ([propDoubleBinℕ]).


These examples are inspired from an old cubicaltt formalization:

https://github.com/mortberg/cubicaltt/blob/master/examples/binnat.ctt

which itself is based on an even older cubical formalization (from 2014):

https://github.com/simhu/cubical/blob/master/examples/binnat.cub



The second representation is more non-standard and inspired by:

https://github.com/RedPRL/redtt/blob/master/library/cool/nats.red

Only some of the experiments have been done for this representation,
but it has the virtue of being a bit simpler to prove equivalent to
ℕ. The same representation can be found in:

http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.BinNat.BinNat where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

-- Positive binary numbers
data Pos : Type₀ where
  pos1 : Pos
  x0   : Pos → Pos
  x1   : Pos → Pos

sucPos : Pos → Pos
sucPos pos1    = x0 pos1
sucPos (x0 ps) = x1 ps
sucPos (x1 ps) = x0 (sucPos ps)

Pos→ℕ : Pos → ℕ
Pos→ℕ pos1    = suc zero
Pos→ℕ (x0 ps) = doubleℕ (Pos→ℕ ps)
Pos→ℕ (x1 ps) = suc (doubleℕ (Pos→ℕ ps))

posInd : {P : Pos → Type₀} → P pos1 → ((p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
posInd {P} h1 hs ps = f ps
  where
  H : (p : Pos) → P (x0 p) → P (x0 (sucPos p))
  H p hx0p = hs (x1 p) (hs (x0 p) hx0p)

  f : (ps : Pos) → P ps
  f pos1    = h1
  f (x0 ps) = posInd (hs pos1 h1) H ps
  f (x1 ps) = hs (x0 ps) (posInd (hs pos1 h1) H ps)

Pos→ℕsucPos : (p : Pos) → Pos→ℕ (sucPos p) ≡ suc (Pos→ℕ p)
Pos→ℕsucPos pos1   = refl
Pos→ℕsucPos (x0 p) = refl
Pos→ℕsucPos (x1 p) = λ i → doubleℕ (Pos→ℕsucPos p i)

zero≠Pos→ℕ : (p : Pos) → ¬ (zero ≡ Pos→ℕ p)
zero≠Pos→ℕ p = posInd (λ prf → znots prf) hs p
  where
  hs : (p : Pos) → ¬ (zero ≡ Pos→ℕ p) → zero ≡ Pos→ℕ (sucPos p) → ⊥
  hs p neq ieq = ⊥-elim (znots (ieq ∙ (Pos→ℕsucPos p)))

ℕ→Pos : ℕ → Pos
ℕ→Pos zero          = pos1
ℕ→Pos (suc zero)    = pos1
ℕ→Pos (suc (suc n)) = sucPos (ℕ→Pos (suc n))

ℕ→PosSuc : ∀ n → ¬ (zero ≡ n) → ℕ→Pos (suc n) ≡ sucPos (ℕ→Pos n)
ℕ→PosSuc zero neq    = ⊥-elim (neq refl)
ℕ→PosSuc (suc n) neq = refl

Pos→ℕ→Pos : (p : Pos) → ℕ→Pos (Pos→ℕ p) ≡ p
Pos→ℕ→Pos p = posInd refl hs p
  where
  hs : (p : Pos) → ℕ→Pos (Pos→ℕ p) ≡ p → ℕ→Pos (Pos→ℕ (sucPos p)) ≡ sucPos p
  hs p hp =
    ℕ→Pos (Pos→ℕ (sucPos p)) ≡⟨ cong ℕ→Pos (Pos→ℕsucPos p) ⟩
    ℕ→Pos (suc (Pos→ℕ p))    ≡⟨ ℕ→PosSuc (Pos→ℕ p) (zero≠Pos→ℕ p) ⟩
    sucPos (ℕ→Pos (Pos→ℕ p)) ≡⟨ cong sucPos hp ⟩
    sucPos p ∎

ℕ→Pos→ℕ : (n : ℕ) → Pos→ℕ (ℕ→Pos (suc n)) ≡ suc n
ℕ→Pos→ℕ zero    = refl
ℕ→Pos→ℕ (suc n) =
  Pos→ℕ (sucPos (ℕ→Pos (suc n))) ≡⟨ Pos→ℕsucPos (ℕ→Pos (suc n)) ⟩
  suc (Pos→ℕ (ℕ→Pos (suc n)))    ≡⟨ cong suc (ℕ→Pos→ℕ n) ⟩
  suc (suc n) ∎

-- Binary numbers
data Binℕ : Type₀ where
  binℕ0   : Binℕ
  binℕpos : Pos → Binℕ

ℕ→Binℕ : ℕ → Binℕ
ℕ→Binℕ zero    = binℕ0
ℕ→Binℕ (suc n) = binℕpos (ℕ→Pos (suc n))

Binℕ→ℕ : Binℕ → ℕ
Binℕ→ℕ binℕ0       = zero
Binℕ→ℕ (binℕpos x) = Pos→ℕ x

ℕ→Binℕ→ℕ : (n : ℕ) → Binℕ→ℕ (ℕ→Binℕ n) ≡ n
ℕ→Binℕ→ℕ zero          = refl
ℕ→Binℕ→ℕ (suc zero)    = refl
ℕ→Binℕ→ℕ (suc (suc n)) =
    Pos→ℕ (sucPos (ℕ→Pos (suc n))) ≡⟨ Pos→ℕsucPos (ℕ→Pos (suc n)) ⟩
    suc (Pos→ℕ (ℕ→Pos (suc n)))    ≡⟨ cong suc (ℕ→Binℕ→ℕ (suc n)) ⟩
    suc (suc n) ∎

Binℕ→ℕ→Binℕ : (n : Binℕ) → ℕ→Binℕ (Binℕ→ℕ n) ≡ n
Binℕ→ℕ→Binℕ binℕ0 = refl
Binℕ→ℕ→Binℕ (binℕpos p) = posInd refl (λ p _ → rem p) p
  where
  rem : (p : Pos) → ℕ→Binℕ (Pos→ℕ (sucPos p)) ≡ binℕpos (sucPos p)
  rem p =
    ℕ→Binℕ (Pos→ℕ (sucPos p))       ≡⟨ cong ℕ→Binℕ (Pos→ℕsucPos p) ⟩
    binℕpos (ℕ→Pos (suc (Pos→ℕ p))) ≡⟨ cong binℕpos ((ℕ→PosSuc (Pos→ℕ p) (zero≠Pos→ℕ p)) ∙
                                                              (cong sucPos (Pos→ℕ→Pos p))) ⟩
    binℕpos (sucPos p) ∎

Binℕ≃ℕ : Binℕ ≃ ℕ
Binℕ≃ℕ = isoToEquiv (iso Binℕ→ℕ ℕ→Binℕ ℕ→Binℕ→ℕ Binℕ→ℕ→Binℕ)

-- Use univalence (in fact only "ua") to get an equality from the
-- above equivalence
Binℕ≡ℕ : Binℕ ≡ ℕ
Binℕ≡ℕ = ua Binℕ≃ℕ

sucBinℕ : Binℕ → Binℕ
sucBinℕ binℕ0       = binℕpos pos1
sucBinℕ (binℕpos x) = binℕpos (sucPos x)

Binℕ→ℕsuc : (x : Binℕ) → suc (Binℕ→ℕ x) ≡ Binℕ→ℕ (sucBinℕ x)
Binℕ→ℕsuc binℕ0       = refl
Binℕ→ℕsuc (binℕpos x) = sym (Pos→ℕsucPos x)

-- We can transport addition on ℕ to Binℕ
_+Binℕ_ : Binℕ → Binℕ → Binℕ
_+Binℕ_ = transport (λ i → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i)) _+_

-- Test: 4 + 1 = 5
private
  _ : binℕpos (x0 (x0 pos1)) +Binℕ binℕpos pos1 ≡ binℕpos (x1 (x0 pos1))
  _ = refl

-- It is easy to test if binary numbers are odd
oddBinℕ : Binℕ → Bool
oddBinℕ binℕ0            = false
oddBinℕ (binℕpos pos1)   = true
oddBinℕ (binℕpos (x0 _)) = false
oddBinℕ (binℕpos (x1 _)) = true

evenBinℕ : Binℕ → Bool
evenBinℕ n = oddBinℕ (sucBinℕ n)

-- And prove the following property (without induction)
oddBinℕnotEvenBinℕ : (n : Binℕ) → oddBinℕ n ≡ not (evenBinℕ n)
oddBinℕnotEvenBinℕ binℕ0            = refl
oddBinℕnotEvenBinℕ (binℕpos pos1)   = refl
oddBinℕnotEvenBinℕ (binℕpos (x0 x)) = refl
oddBinℕnotEvenBinℕ (binℕpos (x1 x)) = refl

-- It is also easy to define and prove the property for unary numbers,
-- however the definition uses recursion and the proof induction
private
  oddn : ℕ → Bool
  oddn zero    = true
  oddn (suc x) = not (oddn x)

  evenn : ℕ → Bool
  evenn n = not (oddn n)

  oddnSuc : (n : ℕ) → oddn n ≡ not (evenn n)
  oddnSuc zero    = refl
  oddnSuc (suc n) = cong not (oddnSuc n)


-- So what we can do instead is to transport the odd test from Binℕ to
-- ℕ along the equality
oddℕ : ℕ → Bool
oddℕ = transport (λ i → Binℕ≡ℕ i → Bool) oddBinℕ

evenℕ : ℕ → Bool
evenℕ = transport (λ i → Binℕ≡ℕ i → Bool) evenBinℕ

-- We can then also transport the property
oddℕnotEvenℕ : (n : ℕ) → oddℕ n ≡ not (evenℕ n)
oddℕnotEvenℕ =
  let -- We first build a path from oddBinℕ to oddℕ. When i=1 this is
      -- "transp (λ j → Binℕ≡ℕ j → Bool) i0 oddBinℕ" (i.e. oddℕ)
      oddp : PathP (λ i → Binℕ≡ℕ i → Bool) oddBinℕ oddℕ
      oddp i = transp (λ j → Binℕ≡ℕ (i ∧ j) → Bool) (~ i) oddBinℕ

      -- We then build a path from evenBinℕ to evenℕ
      evenp : PathP (λ i → Binℕ≡ℕ i → Bool) evenBinℕ evenℕ
      evenp i = transp (λ j → Binℕ≡ℕ (i ∧ j) → Bool) (~ i) evenBinℕ
  in -- Then transport oddBinℕnotEvenBinℕ in a suitable equality type
     -- When i=0 this is "(n : Binℕ) → oddBinℕ n ≡ not (evenBinℕ n)"
     -- When i=1 this is "(n : ℕ) → oddℕ n ≡ not (evenℕ n)"
     transport (λ i → (n : Binℕ≡ℕ i) → oddp i n ≡ not (evenp i n)) oddBinℕnotEvenBinℕ


-- We can do the same for natural numbers:

-- First construct the path
addp : PathP (λ i → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i)) _+_ _+Binℕ_
addp i = transp (λ j → Binℕ≡ℕ (~ i ∨ ~ j) → Binℕ≡ℕ (~ i ∨ ~ j) → Binℕ≡ℕ (~ i ∨ ~ j)) (~ i) _+_

-- Then transport associativity:
+Binℕ-assoc : ∀ m n o → m +Binℕ (n +Binℕ o) ≡ (m +Binℕ n) +Binℕ o
+Binℕ-assoc =
  transport (λ i → (m n o : Binℕ≡ℕ (~ i))
                 → addp i m (addp i n o) ≡ addp i (addp i m n) o) +-assoc


-- We can also define what it means to be an implementation of natural
-- numbers and use this to transport properties between different
-- implementation of natural numbers. This can be seen as a special
-- case of the structure identity principle: any property that holds
-- for one structure also holds for an equivalent one.

-- An implementation of natural numbers (i.e. a "natural number
-- structure") has a zero and successor.
record NatImpl (A : Type₀) : Type₀ where
  field
    z : A
    s : A → A
open NatImpl

NatImplℕ : NatImpl ℕ
z NatImplℕ = zero
s NatImplℕ = suc

NatImplBinℕ : NatImpl Binℕ
z NatImplBinℕ = binℕ0
s NatImplBinℕ = sucBinℕ

-- Using the equality between binary and unary numbers we can get an
-- equality between the two implementations of the NatImpl interface
NatImplℕ≡Binℕ : PathP (λ i → NatImpl (Binℕ≡ℕ (~ i))) NatImplℕ NatImplBinℕ
z (NatImplℕ≡Binℕ i) = transp (λ j → Binℕ≡ℕ (~ i ∨ ~ j)) (~ i) zero
s (NatImplℕ≡Binℕ i) =
  λ x → glue (λ { (i = i0) → suc x
                ; (i = i1) → sucBinℕ x })
             -- We need to do use and hcomp to do and endpoint
             -- correction as "suc (unglue x)" connects "suc x"
             -- with "suc (Binℕ→ℕ x)" along i (which makes sense as
             -- x varies from ℕ to Binℕ along i), but we need
             -- something from "suc x" to "Binℕ→ℕ (sucBinℕ x)" for
             -- the glue to be well-formed
             (hcomp (λ j → λ { (i = i0) → suc x
                             ; (i = i1) → Binℕ→ℕsuc x j })
                    (suc (unglue (i ∨ ~ i) x)))

-- We then use this to transport +-suc from unary to binary numbers
+Binℕ-suc : ∀ m n → m +Binℕ sucBinℕ n ≡ sucBinℕ (m +Binℕ n)
+Binℕ-suc =
  transport (λ i → (m n : Binℕ≡ℕ (~ i))
                 → addp i m (NatImplℕ≡Binℕ i .s n) ≡ NatImplℕ≡Binℕ i .s (addp i m n)) +-suc



-- Doubling experiment: we define a notion of "doubling structure" and
-- transport a proof that is proved directly using refl for binary
-- numbers to unary numbers. This is an example of program/data
-- refinement: we can use univalence to prove properties about
-- inefficient data-structures using efficient ones.

-- Doubling structures
record Double {ℓ} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    -- doubling function computing 2 * x
    double : A → A
    -- element to double
    elt : A
open Double

-- Compute: 2^n * x
doubles : ∀ {ℓ} {A : Type ℓ} (D : Double A) → ℕ → A → A
doubles D n x = iter n (double D) x

Doubleℕ : Double ℕ
double Doubleℕ = doubleℕ
elt Doubleℕ    = n1024
  where
  -- 1024 = 2^8 * 2^2 = 2^10
  n1024 : ℕ
  n1024 = doublesℕ 8 4

-- The doubling operation on binary numbers is O(1), while for unary
-- numbers it is O(n). What is of course even more problematic is that
-- we cannot handle very big unary natural numbers, but with binary
-- there is no problem to represent very big numbers
doubleBinℕ : Binℕ → Binℕ
doubleBinℕ binℕ0       = binℕ0
doubleBinℕ (binℕpos x) = binℕpos (x0 x)

DoubleBinℕ : Double Binℕ
double DoubleBinℕ = doubleBinℕ
elt DoubleBinℕ    = bin1024
  where
  -- 1024 = 2^10 = 10000000000₂
  bin1024 : Binℕ
  bin1024 = binℕpos (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 pos1))))))))))

-- As these function don't commute strictly we have to prove it
-- separately and insert it in the proof of DoubleBinℕ≡Doubleℕ below
-- (just like we had to in NatImplℕ≡NatImplBinℕ
Binℕ→ℕdouble : (x : Binℕ) → doubleℕ (Binℕ→ℕ x) ≡ Binℕ→ℕ (doubleBinℕ x)
Binℕ→ℕdouble binℕ0       = refl
Binℕ→ℕdouble (binℕpos x) = refl

-- We use the equality between Binℕ and ℕ to get an equality of
-- doubling structures
DoubleBinℕ≡Doubleℕ : PathP (λ i → Double (Binℕ≡ℕ i)) DoubleBinℕ Doubleℕ
double (DoubleBinℕ≡Doubleℕ i) =
  λ x → glue (λ { (i = i0) → doubleBinℕ x
                ; (i = i1) → doubleℕ x })
             (hcomp (λ j → λ { (i = i0) → Binℕ→ℕdouble x j
                             ; (i = i1) → doubleℕ x })
                    (doubleℕ (unglue (i ∨ ~ i) x)))
elt (DoubleBinℕ≡Doubleℕ i) = transp (λ j → Binℕ≡ℕ (i ∨ ~ j)) i (Doubleℕ .elt)

-- We can now use transport to prove a property that is too slow to
-- check with unary numbers. We define the property we want to check
-- as a record so that Agda does not try to unfold it eagerly.
record propDouble {ℓ} {A : Type ℓ} (D : Double A) : Type ℓ where
  field
  -- 2^20 * e = 2^5 * (2^15 * e)
    proof : doubles D 20 (elt D) ≡ doubles D 5 (doubles D 15 (elt D))
open propDouble

-- The property we want to prove takes too long to typecheck for ℕ:
-- propDoubleℕ : propDouble Doubleℕ
-- propDoubleℕ = refl

-- With binary numbers it is instant
propDoubleBinℕ : propDouble DoubleBinℕ
proof propDoubleBinℕ = refl

-- By transporting the proof along the equality we then get it for
-- unary numbers
propDoubleℕ : propDouble Doubleℕ
propDoubleℕ = transport (λ i → propDouble (DoubleBinℕ≡Doubleℕ i)) propDoubleBinℕ


--------------------------------------------------------------------------------
--
-- Alternative encoding of binary natural numbers inspired by:
-- https://github.com/RedPRL/redtt/blob/master/library/cool/nats.red
--
-- This representation makes the equivalence with ℕ a bit easier to
-- prove, but the doubling example wouldn't work as nicely as we
-- cannot define it as an O(1) operation

data binnat : Type₀ where
  zero     : binnat            -- 0
  consOdd  : binnat → binnat   -- 2^n + 1
  consEven : binnat → binnat   -- 2^{n+1}

binnat→ℕ : binnat → ℕ
binnat→ℕ zero         = 0
binnat→ℕ (consOdd n)  = suc (doubleℕ (binnat→ℕ n))
binnat→ℕ (consEven n) = suc (suc (doubleℕ (binnat→ℕ n)))

suc-binnat : binnat → binnat
suc-binnat zero         = consOdd zero
suc-binnat (consOdd n)  = consEven n
suc-binnat (consEven n) = consOdd (suc-binnat n)

ℕ→binnat : ℕ → binnat
ℕ→binnat zero    = zero
ℕ→binnat (suc n) = suc-binnat (ℕ→binnat n)

binnat→ℕ-suc : (n : binnat) → binnat→ℕ (suc-binnat n) ≡ suc (binnat→ℕ n)
binnat→ℕ-suc zero         = refl
binnat→ℕ-suc (consOdd n)  = refl
binnat→ℕ-suc (consEven n) = λ i → suc (doubleℕ (binnat→ℕ-suc n i))

ℕ→binnat→ℕ : (n : ℕ) → binnat→ℕ (ℕ→binnat n) ≡ n
ℕ→binnat→ℕ zero    = refl
ℕ→binnat→ℕ (suc n) = (binnat→ℕ-suc (ℕ→binnat n)) ∙ (cong suc (ℕ→binnat→ℕ n))

suc-ℕ→binnat-double : (n : ℕ) → suc-binnat (ℕ→binnat (doubleℕ n)) ≡ consOdd (ℕ→binnat n)
suc-ℕ→binnat-double zero    = refl
suc-ℕ→binnat-double (suc n) = λ i → suc-binnat (suc-binnat (suc-ℕ→binnat-double n i))

binnat→ℕ→binnat : (n : binnat) → ℕ→binnat (binnat→ℕ n) ≡ n
binnat→ℕ→binnat zero        = refl
binnat→ℕ→binnat (consOdd n) =
           (suc-ℕ→binnat-double (binnat→ℕ n)) ∙ (cong consOdd (binnat→ℕ→binnat n))
binnat→ℕ→binnat (consEven n) =
           (λ i → suc-binnat (suc-ℕ→binnat-double (binnat→ℕ n) i)) ∙ (cong consEven (binnat→ℕ→binnat n))

ℕ≃binnat : ℕ ≃ binnat
ℕ≃binnat = isoToEquiv (iso ℕ→binnat binnat→ℕ binnat→ℕ→binnat ℕ→binnat→ℕ)

ℕ≡binnat : ℕ ≡ binnat
ℕ≡binnat = ua ℕ≃binnat

-- We can transport addition on ℕ to binnat
_+binnat_ : binnat → binnat → binnat
_+binnat_ = transport (λ i → ℕ≡binnat i → ℕ≡binnat i → ℕ≡binnat i) _+_

-- Test: 4 + 1 = 5
_ : consEven (consOdd zero) +binnat consOdd zero ≡ consOdd (consEven zero)
_ = refl

oddbinnat : binnat → Bool
oddbinnat zero         = false
oddbinnat (consOdd _)  = true
oddbinnat (consEven _) = false

oddℕ' : ℕ → Bool
oddℕ' = transport (λ i → ℕ≡binnat (~ i) → Bool) oddbinnat

-- The NatImpl example for this representation of binary numbers
private
  NatImplbinnat : NatImpl binnat
  z NatImplbinnat = zero
  s NatImplbinnat = suc-binnat

  -- Note that the s case is a bit simpler as no end-point correction
  -- is necessary (things commute strictly)
  NatImplℕ≡NatImplbinnat : PathP (λ i → NatImpl (ℕ≡binnat i)) NatImplℕ NatImplbinnat
  z (NatImplℕ≡NatImplbinnat i) = transp (λ j → ℕ≡binnat (i ∨ ~ j)) i zero
  s (NatImplℕ≡NatImplbinnat i) =
    λ x → glue (λ { (i = i0) → suc x
                  ; (i = i1) → suc-binnat x })
               (suc-binnat (unglue (i ∨ ~ i) x))

  oddSuc : (n : binnat) → oddbinnat n ≡ not (oddbinnat (suc-binnat n))
  oddSuc zero         = refl
  oddSuc (consOdd _)  = refl
  oddSuc (consEven _) = refl

  oddℕSuc' : (n : ℕ) → oddℕ' n ≡ not (oddℕ' (suc n))
  oddℕSuc' =
    let eq : (i : I) → ℕ≡binnat (~ i) → Bool
        eq i = transp (λ j → ℕ≡binnat (~ i ∨ ~ j) → Bool) (~ i) oddbinnat
    in transport
         (λ i → (n : ℕ≡binnat (~ i)) → eq i n ≡ not (eq i (NatImplℕ≡NatImplbinnat (~ i) .NatImpl.s n)))
         oddSuc
