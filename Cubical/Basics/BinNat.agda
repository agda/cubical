{-# OPTIONS --cubical --no-exact-split #-}
module Cubical.Basics.BinNat where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Nat
open import Cubical.Basics.Empty
open import Cubical.Basics.Equiv

-- Positive binary numbers
data Pos : Set where
  pos1 : Pos
  x0 : Pos -> Pos
  x1 : Pos -> Pos

sucPos : Pos → Pos
sucPos pos1    = x0 pos1
sucPos (x0 ps) = x1 ps
sucPos (x1 ps) = x0 (sucPos ps)

posToℕ : Pos → ℕ
posToℕ pos1    = suc zero
posToℕ (x0 ps) = doubleℕ (posToℕ ps)
posToℕ (x1 ps) = suc (doubleℕ (posToℕ ps))

posInd : {P : Pos → Set} → P pos1 → ((p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
posInd {P} h1 hs ps = f ps
  where
  H : (p : Pos) → P (x0 p) → P (x0 (sucPos p))
  H p hx0p = hs (x1 p) (hs (x0 p) hx0p)

  f : (ps : Pos) → P ps
  f pos1 = h1
  f (x0 ps) = posInd (hs pos1 h1) H ps
  f (x1 ps) = hs (x0 ps) (posInd (hs pos1 h1) H ps)

sucPosSuc : (p : Pos) → posToℕ (sucPos p) ≡ suc (posToℕ p)
sucPosSuc pos1   = refl
sucPosSuc (x0 p) = refl
sucPosSuc (x1 p) = λ i → doubleℕ (sucPosSuc p i)

zeronPosToN : (p : Pos) → ¬ (zero ≡ posToℕ p)
zeronPosToN p = posInd (λ prf → znots prf) hs p
  where
  hs : (p : Pos) → ¬ (zero ≡ posToℕ p) → zero ≡ posToℕ (sucPos p) → ⊥
  hs p neq ieq = ⊥-elim (znots (compPath ieq (sucPosSuc p)))

ntoPos : ℕ → Pos
ntoPos zero    = pos1
ntoPos (suc zero) = pos1
ntoPos (suc (suc n)) = sucPos (ntoPos (suc n))


ntoPosSuc : ∀ n → ¬ (zero ≡ n) → ntoPos (suc n) ≡ sucPos (ntoPos n)
ntoPosSuc zero neq    = ⊥-elim (neq refl)
ntoPosSuc (suc n) neq = refl

ntoPosK : (p : Pos) → ntoPos (posToℕ p) ≡ p
ntoPosK p = posInd refl hs p
  where
  hs : (p : Pos) → ntoPos (posToℕ p) ≡ p → ntoPos (posToℕ (sucPos p)) ≡ sucPos p
  hs p hp =
    ntoPos (posToℕ (sucPos p)) ≡⟨ cong ntoPos (sucPosSuc p) ⟩
    ntoPos (suc (posToℕ p))    ≡⟨ ntoPosSuc (posToℕ p) (zeronPosToN p) ⟩
    sucPos (ntoPos (posToℕ p)) ≡⟨ cong sucPos hp ⟩
    sucPos p ∎

posToNK : ∀ n → posToℕ (ntoPos (suc n)) ≡ suc n
posToNK zero = refl
posToNK (suc n) =
  posToℕ (sucPos (ntoPos (suc n))) ≡⟨ sucPosSuc (ntoPos (suc n)) ⟩
  suc (posToℕ (ntoPos (suc n))) ≡⟨ cong suc (posToNK n) ⟩
  suc (suc n) ∎

-- Binary numbers
data Binℕ : Set where
  binℕ0   : Binℕ
  binℕpos : Pos → Binℕ

ntoBinN : ℕ → Binℕ
ntoBinN zero    = binℕ0
ntoBinN (suc n) = binℕpos (ntoPos (suc n))

binNtoN : Binℕ → ℕ
binNtoN binℕ0       = zero
binNtoN (binℕpos x) = posToℕ x

ntoBinNK : (n : ℕ) → binNtoN (ntoBinN n) ≡ n
ntoBinNK zero          = refl
ntoBinNK (suc zero)    = refl
ntoBinNK (suc (suc n)) =
    posToℕ (sucPos (ntoPos (suc n))) ≡⟨ sucPosSuc (ntoPos (suc n)) ⟩
    suc (posToℕ (ntoPos (suc n)))    ≡⟨ cong suc (ntoBinNK (suc n)) ⟩
    suc (suc n)       ∎

binNtoNK : ∀ b → ntoBinN (binNtoN b) ≡ b
binNtoNK binℕ0 = refl
binNtoNK (binℕpos p) = posInd refl (λ p _ → rem p) p
  where
  rem : (p : Pos) → ntoBinN (posToℕ (sucPos p)) ≡ binℕpos (sucPos p)
  rem p =
    ntoBinN (posToℕ (sucPos p)) ≡⟨ cong ntoBinN (sucPosSuc p) ⟩
    binℕpos (ntoPos (suc (posToℕ p))) ≡⟨ cong binℕpos (compPath (ntoPosSuc (posToℕ p) (zeronPosToN p))
                                                        (cong sucPos (ntoPosK p))) ⟩
    binℕpos (sucPos p) ∎

Binℕ≃ℕ : Binℕ ≃ ℕ
Binℕ≃ℕ = isoToEquiv binNtoN ntoBinN ntoBinNK binNtoNK

Binℕ≡ℕ : Binℕ ≡ ℕ
Binℕ≡ℕ = isoToPath binNtoN ntoBinN ntoBinNK binNtoNK

doubleBinℕ : Binℕ → Binℕ
doubleBinℕ binℕ0 = binℕ0
doubleBinℕ (binℕpos x) = binℕpos (x0 x)

doublesBinℕ : ℕ → Binℕ → Binℕ
doublesBinℕ zero b = b
doublesBinℕ (suc n) b = doublesBinℕ n (doubleBinℕ b)


-- Doubling structure
-- TODO: this could be a record?
data Double : Set (ℓ-suc ℓ-zero) where
  dC : (A : Set)           -- carrier
      → (double : A -> A) -- doubling function computing 2 * x
      → (elt : A)         -- element to double
      → Double

carrier : Double -> Set
carrier (dC c _ _) = c

double : (D : Double) -> (carrier D -> carrier D)
double (dC _ op _) = op

elt : (D : Double) -> carrier D
elt (dC _ _ e) = e

DoubleN : Double
DoubleN = dC ℕ doubleℕ n1024

bin1024 : Binℕ
bin1024 = binℕpos (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 pos1))))))))))

DoubleBinN : Double
DoubleBinN = dC Binℕ doubleBinℕ bin1024

-- Compute: 2^n * x
doubles : ∀ D → (n : ℕ) → carrier D → carrier D
doubles D n x = iter n (double D) x

-- 2^20 * e = 2^5 * (2^15 * e)

propDouble : Double → Set
propDouble D = doubles D 20 (elt D) ≡ doubles D 5 (doubles D 15 (elt D))

-- The property we want to prove that takes long to typecheck:
-- 2^10 * 1024 = 2^5 * (2^5 * 1024)
--
-- propN : propDouble DoubleN
-- propN = refl


-- With binary numbers it is instant
propBin : propDouble DoubleBinN
propBin = refl

-- Define intermediate structure:
doubleBinN' : Binℕ → Binℕ
doubleBinN' b = ntoBinN (doubleℕ (binNtoN b))

DoubleBinN' : Double
DoubleBinN' = dC Binℕ doubleBinN' (ntoBinN n1024)

-- eqDouble1 : DoubleN ≡ DoubleBinN'
-- eqDouble1 = elimIsoInv (λ f g → DoubleN ≡ (dC _ (λ x → f (doubleN (g x))) (f n1024))) refl ntoBinN binNtoN binNtoNK ntoBinNK

-- eqDouble2 : DoubleBinN' ≡ DoubleBinN
-- eqDouble2 = cong F rem where
--   F : (BinN → BinN) → Double
--   F d = dC _ d (ntoBinN n1024)
--   rem : doubleBinN' ≡ doubleBinN
--   rem = funExt rem1 where
--     rem1 : ∀ n → (doubleBinN' n) ≡ (doubleBinN n)
--     rem1 binN0 i = binN0
--     rem1 (binNpos x) = lem1 (x0 x)

-- eqDouble : DoubleN ≡ DoubleBinN
-- eqDouble = trans eqDouble1 eqDouble2

-- propDoubleImpl : propDouble DoubleBinN → propDouble DoubleN
-- propDoubleImpl x = subst {P = propDouble} (sym eqDouble) x

-- goal : propDouble DoubleN
-- goal = propDoubleImpl propBin



-- Different encoding inspired by:
-- https://github.com/RedPRL/redtt/blob/master/library/cool/nats.red
data binnat : Set where
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
ℕ→binnat→ℕ (suc n) = compPath (binnat→ℕ-suc (ℕ→binnat n)) (cong suc (ℕ→binnat→ℕ n))

suc-ℕ→binnat-double : (n : ℕ) → suc-binnat (ℕ→binnat (doubleℕ n)) ≡ consOdd (ℕ→binnat n)
suc-ℕ→binnat-double zero    = refl
suc-ℕ→binnat-double (suc n) = λ i → suc-binnat (suc-binnat (suc-ℕ→binnat-double n i))

binnat→ℕ→binnat : (n : binnat) → ℕ→binnat (binnat→ℕ n) ≡ n
binnat→ℕ→binnat zero        = refl
binnat→ℕ→binnat (consOdd n) =
  compPath (suc-ℕ→binnat-double (binnat→ℕ n))
           (cong consOdd (binnat→ℕ→binnat n))
binnat→ℕ→binnat (consEven n) =
  compPath (λ i → suc-binnat (suc-ℕ→binnat-double (binnat→ℕ n) i))
           (cong consEven (binnat→ℕ→binnat n))

ℕ≃binnat : ℕ ≃ binnat
ℕ≃binnat = isoToEquiv ℕ→binnat binnat→ℕ binnat→ℕ→binnat ℕ→binnat→ℕ

ℕ≡binnat : ℕ ≡ binnat
ℕ≡binnat = isoToPath ℕ→binnat binnat→ℕ binnat→ℕ→binnat ℕ→binnat→ℕ
