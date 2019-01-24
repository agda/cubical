{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Basics.BinNat where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Nat
open import Cubical.Basics.Bool
open import Cubical.Basics.Empty
open import Cubical.Basics.Equiv
open import Cubical.Basics.Univalence

-- Encoding of binary natural numbers inspired by:
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
ℕ≡binnat = ua ℕ≃binnat

-- We can transport addition on ℕ to binnat
_+binnat_ : binnat → binnat → binnat
_+binnat_ = transp (λ i → ℕ≡binnat i → ℕ≡binnat i → ℕ≡binnat i) i0 _+_

-- TODO: prove   _+binnat_ ≡ _+_

-- Test: 4 + 1 = 5
_ : consEven (consOdd zero) +binnat consOdd zero ≡ consOdd (consEven zero)
_ = refl


oddbinnat : binnat → Bool
oddbinnat zero         = false
oddbinnat (consOdd _)  = true
oddbinnat (consEven _) = false

oddℕ : ℕ → Bool
oddℕ = transp (λ i → ℕ≡binnat (~ i) → Bool) i0 oddbinnat

module _ where
  -- Define what it means to be an interface for natural numbers
  record impl (A : Set) : Set where
    field
      z : A
      s : A → A

  implℕ : impl ℕ
  implℕ = record { z = zero
                 ; s = suc }

  implbinnat : impl binnat
  implbinnat = record { z = zero
                      ; s = suc-binnat }

  implℕ≡implbinnat : PathP (λ i → impl (ℕ≡binnat i)) implℕ implbinnat
  implℕ≡implbinnat i = record { z = transp (λ j → ℕ≡binnat (i ∨ ~ j)) i zero
                              -- This glue trick is very neat!
                              ; s = λ x → glue (λ { (i = i0) → suc x
                                                  ; (i = i1) → suc-binnat x })
                                               (suc-binnat (unglue {φ = i ∨ ~ i} x)) }

  oddSuc : (n : binnat) → oddbinnat n ≡ not (oddbinnat (suc-binnat n))
  oddSuc zero         = refl
  oddSuc (consOdd _)  = refl
  oddSuc (consEven _) = refl

  -- TODO: upstream somewhere? It's a bit useless, bit maybe intructive...
  transpNeg : ∀ {ℓ} (A : I → Set ℓ) (φ : I) (a : A i1) → A i0
  transpNeg A φ a = transp (λ i → A (~ i)) i0 a

  -- TODO: clean, maybe define "transpNegFill"
  oddℕSuc : (n : ℕ) → oddℕ n ≡ not (oddℕ (suc n))
  oddℕSuc =
    let eq : (i : I) → ℕ≡binnat i → Bool
        eq i = transp (λ j → ℕ≡binnat (i ∨ ~ j) → Bool) i oddbinnat
    in transp (λ i → (n : ℕ≡binnat (~ i)) → eq (~ i) n ≡ not (eq (~ i) (implℕ≡implbinnat (~ i) .impl.s n) )) i0 oddSuc

  -- TODO: do the doubling experiment

-- Doubling structure
record Double : Set (ℓ-suc ℓ-zero) where
  constructor dC
  field
    carrier : Set
    -- doubling function computing 2 * x
    double : carrier -> carrier
    -- element to double
    elt : carrier
open Double

-- 1024 = 2^8 * 2^2 = 2^10
n1024 : ℕ
n1024 = doublesℕ 8 4

Doubleℕ : Double
Doubleℕ = dC ℕ doubleℕ n1024

binnat1024 : binnat
binnat1024 = consEven (consOdd (consOdd (consOdd (consOdd (consOdd (consOdd (consOdd (consOdd (consOdd zero)))))))))



------------------------------------------------------------------------------

-- Alternative version inspired by an old cubicaltt formalization:
-- https://github.com/mortberg/cubicaltt/blob/master/examples/binnat.ctt

-- This encoding is a lot harder to work with than the one above.


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

private
  bin1024 : Binℕ
  bin1024 = binℕpos (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 pos1))))))))))

  DoubleBinN : Double
  DoubleBinN = dC Binℕ doubleBinℕ bin1024

-- Compute: 2^n * x
doubles : ∀ D → (n : ℕ) → carrier D → carrier D
doubles D n x = iter n (double D) x

-- TODO: upstream
idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
idfun _ x = x

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  section : (f : A → B) → (g : B → A) → Set ℓb
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Set ℓa
  retract f g = ∀ a → g (f a) ≡ a
  
substInv : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {a x : A} (p : a ≡ x) → P x → P a
substInv P p px = subst P (sym p) px

elimEquiv : ∀ {ℓ ℓ'} → {B : Set ℓ} (P : {A : Set ℓ} → (A → B) → Set ℓ') → (d : P (idfun B))
          → {A : Set ℓ} → (e : A ≃ B) → P (e .fst)
elimEquiv {ℓ} {ℓ'} {B} P d {A} e = rem
  where
    T : (Σ (Set ℓ) (λ X → X ≃ B)) → Set ℓ'
    T x = P (x .snd .fst)
    rem1 : (B , idEquiv B) ≡ (A , e)
    rem1 = contrSinglEquiv e
    rem : P (e .fst)
    rem = subst T rem1 d

con : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isEquiv f → A ≃ B
con f p = f , p


elimIso : ∀{ℓ ℓ'} → {B : Set ℓ} → (Q : {A : Set ℓ} → (A → B) → (B → A) → Set ℓ') → (h : Q (idfun B) (idfun B))
          → {A : Set ℓ} → (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
elimIso {ℓ} {ℓ'} {B} Q h {A} f g sfg rfg = rem1 f g sfg rfg where
  P : {A : Set ℓ} → (f : A -> B) → Set (ℓ-max ℓ' ℓ)
  P {A} f = (g : B -> A) -> section f g -> retract f g -> Q f g

  rem : P (idfun B)
  rem g sfg rfg = substInv (Q (idfun B)) (λ i → λ b → (sfg b) i) h

  rem1 : {A : Set ℓ} → (f : A -> B) → P f
  rem1 f g sfg rfg = 
    elimEquiv P rem (con f (isoToIsEquiv f g sfg rfg)) g sfg rfg

elimIsoInv : ∀{ℓ ℓ'} → {A : Set ℓ} → (Q : {B : Set ℓ} → (A → B) → (B → A) → Set ℓ') → (h : Q (idfun A) (idfun A))
               → {B : Set ℓ} → (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
elimIsoInv {A = A} Q h {B} f g sfg rfg = elimIso (λ f g → Q g f) h g f rfg sfg

private
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

  EquivInvFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A ≃ B) → B → A
  EquivInvFun f b = f .snd .equiv-proof b .fst .fst

  eqDouble1 : Doubleℕ ≡ DoubleBinN'
  eqDouble1 = elimIsoInv (λ f g → Doubleℕ ≡ (dC _ (λ x → f (doubleℕ (g x))) (f n1024))) refl ntoBinN binNtoN binNtoNK ntoBinNK

  lem1 : ∀ p → ntoBinN (posToℕ p) ≡ binℕpos p
  lem1 p = posInd refl (λ p _ → rem p) p where
    rem : (p : Pos) → ntoBinN (posToℕ (sucPos p)) ≡ binℕpos (sucPos p)
    rem p = compPath rem1 rem2 where
      rem1 = cong ntoBinN (sucPosSuc p)
      rem2 : binℕpos (ntoPos (suc (posToℕ p))) ≡ binℕpos (sucPos p)
      rem2 = λ i → binℕpos (compPath (ntoPosSuc (posToℕ p) (zeronPosToN p)) (cong sucPos (ntoPosK p)) i)

  eqDouble2 : DoubleBinN' ≡ DoubleBinN
  eqDouble2 = cong F rem where
    F : (Binℕ → Binℕ) → Double
    F d = dC _ d (ntoBinN n1024)
    rem : doubleBinN' ≡ doubleBinℕ
    rem = funExt rem1
      where
      rem1 : ∀ n → (doubleBinN' n) ≡ (doubleBinℕ n)
      rem1 binℕ0 = refl
      rem1 (binℕpos x) = lem1 (x0 x)

  eqDouble : Doubleℕ ≡ DoubleBinN
  eqDouble = compPath eqDouble1 eqDouble2
  
  propDoubleImpl : propDouble DoubleBinN → propDouble Doubleℕ
  propDoubleImpl x = subst propDouble (sym eqDouble) x
  
  goal : propDouble Doubleℕ
  goal = propDoubleImpl propBin
