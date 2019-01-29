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


unglueua : ∀ {A B : Set} → (e : A ≃ B) → (i : I) (x : ua e i) → B [ i ∨ ~ i ↦ (λ { (i = i0) → e .fst x ; (i = i1) → x }) ]
unglueua e i x = inc (unglue {φ = i ∨ ~ i} x)


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


------------------------------------------------------------------------------

-- Inspired by an old cubicaltt formalization:
-- https://github.com/mortberg/cubicaltt/blob/master/examples/binnat.ctt

-- Positive binary numbers
data Pos : Set where
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

posInd : {P : Pos → Set} → P pos1 → ((p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
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
  hs p neq ieq = ⊥-elim (znots (compPath ieq (Pos→ℕsucPos p)))

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
data Binℕ : Set where
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
    suc (suc n)       ∎

Binℕ→ℕ→Binℕ : (n : Binℕ) → ℕ→Binℕ (Binℕ→ℕ n) ≡ n
Binℕ→ℕ→Binℕ binℕ0 = refl
Binℕ→ℕ→Binℕ (binℕpos p) = posInd refl (λ p _ → rem p) p
  where
  rem : (p : Pos) → ℕ→Binℕ (Pos→ℕ (sucPos p)) ≡ binℕpos (sucPos p)
  rem p =
    ℕ→Binℕ (Pos→ℕ (sucPos p))       ≡⟨ cong ℕ→Binℕ (Pos→ℕsucPos p) ⟩
    binℕpos (ℕ→Pos (suc (Pos→ℕ p))) ≡⟨ cong binℕpos (compPath (ℕ→PosSuc (Pos→ℕ p) (zero≠Pos→ℕ p))
                                                              (cong sucPos (Pos→ℕ→Pos p))) ⟩
    binℕpos (sucPos p) ∎

Binℕ≃ℕ : Binℕ ≃ ℕ
Binℕ≃ℕ = isoToEquiv Binℕ→ℕ ℕ→Binℕ ℕ→Binℕ→ℕ Binℕ→ℕ→Binℕ

Binℕ≡ℕ : Binℕ ≡ ℕ
Binℕ≡ℕ = ua Binℕ≃ℕ



-- Doubling experiment

-- Doubling structure
record Double {ℓ} (A : Set ℓ) : Set (ℓ-suc ℓ) where
  constructor dC
  field
    -- doubling function computing 2 * x
    double : A → A
    -- element to double
    elt : A
open Double

-- Compute: 2^n * x
doubles : ∀ {ℓ} {A : Set ℓ} (D : Double A) → ℕ → A → A
doubles D n x = iter n (double D) x

doubleBinℕ : Binℕ → Binℕ
doubleBinℕ binℕ0       = binℕ0
doubleBinℕ (binℕpos x) = binℕpos (x0 x)

Doubleℕ : Double ℕ
double Doubleℕ = doubleℕ
elt Doubleℕ = n1024
-- Doubleℕ = dC doubleℕ n1024
  where
  -- 1024 = 2^8 * 2^2 = 2^10
  n1024 : ℕ
  n1024 = doublesℕ 8 4

DoubleBinℕ : Double Binℕ
DoubleBinℕ = dC doubleBinℕ bin1024
  where
  -- 1024 = 10000000000 = 2^10
  bin1024 : Binℕ
  bin1024 = binℕpos (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 (x0 pos1))))))))))

-- As these don't commute strictly we have to prove it separately and
-- insert it in the proof of DoubleBinℕ≡Doubleℕ below
Binℕ→ℕdouble : (x : Binℕ) → doubleℕ (Binℕ→ℕ x) ≡ Binℕ→ℕ (doubleBinℕ x)
Binℕ→ℕdouble binℕ0       = refl
Binℕ→ℕdouble (binℕpos x) = refl
  
DoubleBinℕ≡Doubleℕ : PathP (λ i → Double (Binℕ≡ℕ i)) DoubleBinℕ Doubleℕ
DoubleBinℕ≡Doubleℕ i =
  dC (λ x → glue (λ { (i = i0) → doubleBinℕ x
                    ; (i = i1) → doubleℕ x })
                 (hcomp (λ j → λ { (i = i0) → Binℕ→ℕdouble x j
                                 ; (i = i1) → doubleℕ x })
                        (doubleℕ (unglue {φ = i ∨ ~ i} x))))
     (transp (λ j → Binℕ≡ℕ (i ∨ ~ j)) i (Doubleℕ .elt)) 



-- 2^20 * e = 2^5 * (2^15 * e)
propDouble : ∀ {ℓ} {A : Set ℓ} → Double A → Set ℓ
propDouble D = doubles D 20 (elt D) ≡ doubles D 5 (doubles D 15 (elt D))

-- The property we want to prove that takes long to typecheck for ℕ:
-- 2^10 * 1024 = 2^5 * (2^5 * 1024)
--
-- propDoubleℕ : propDouble Doubleℕ
-- propDoubleℕ = refl

-- With binary numbers it is instant
propDoubleBinℕ : propDouble DoubleBinℕ
propDoubleBinℕ = refl

-- Why is this not typechecking fast?
-- It seems like Agda is eagerly unfolding "propDouble Doubleℕ" ?
-- propDoubleℕ : propDouble Doubleℕ
-- propDoubleℕ = transp (λ i → propDouble (DoubleBinℕ≡Doubleℕ i)) propDoubleBinℕ






-- TODO: clean the rest of the file and do some examples for Binℕ


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
                              ; s = -- \ x → {!unglue {φ = i ∨ ~ i} x!}
                                      λ x → glue (λ { (i = i0) → suc x
                                                    ; (i = i1) → suc-binnat x })
                                               (suc-binnat (unglue {φ = i ∨ ~ i} x))
                                               }

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
