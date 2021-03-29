{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Delooping.n.base where

open import Cubical.HITs.Susp
open import Cubical.Data.Int
open import Cubical.HITs.Pushout
open import Cubical.Data.Nat hiding (elim ; _·_) renaming (_+_ to _+N_ ; +-comm to +N-comm ; ·-comm to ·ℕ-comm ; +-assoc to +ℕ-assoc)
-- open import Cubical.Foundation.Prelims
open import Cubical.Foundations.Everything


open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary

ℤ/'_ : (n : ℕ) → Type₀
ℤ/' n = Int / λ x b → (pos n + x) ≡ b


add_ : (b : ℕ) → Int → Int
(add n) m = (pos n) + m

{-
pos+ : (n a : ℕ) → pos (n + a) ≡ (pos n + pos a)
pos+ n zero = cong pos (+-comm n zero)
pos+ n (suc a) = cong pos (+-suc n a) ∙ cong sucInt (pos+ n a)

pos- : (n a : ℕ) → pos ((add n) a) - pos n ≡ pos (idfun ℕ a)
pos- n a = (λ i → pos+ n a i - pos n)
        ∙∙ (λ i → (+-comm (pos n) (pos a) i) - pos n)
        ∙∙ plusMinus (pos n) (pos a)
-}

data ℤ/_ (n : ℕ) : Type₀ where
  [_] : Int → ℤ/ n
  kill-l : (x : Int) → [ pos n + x ] ≡ [ x ]
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

_≤_ : (z y : Int) → Type₀
_≤_ z y = Σ[ n ∈ ℕ ] z + pos n ≡ y

_<_ : (z y : Int) → Type₀
_<_ z y = Σ[ n ∈ ℕ ] pos (suc n) + z ≡ y

dec≤ : (x y : Int) → (y ≤ x) ⊎ (x < y)
dec≤ (pos zero) (pos zero) = inl (0 , refl)
dec≤ (pos zero) (pos (suc m)) = inr (m , refl)
dec≤ (pos (suc n)) (pos zero) = inl ((suc n) , +-comm 0 (pos (suc n)))
dec≤ (pos (suc n)) (pos (suc m)) with dec≤ (pos n) (pos m)
... | inl p = inl ((fst p) , sym (sucInt+ (pos m) (pos (fst p))) ∙ cong sucInt (snd p))
... | inr p = inr ((fst p) , cong sucInt (snd p))
dec≤ (pos n) (negsuc m) = inl (m +N (suc n) , {!!})
dec≤ (negsuc n) (pos n₁) = {!!}
dec≤ (negsuc n) (negsuc n₁) = {!!}

private
  lem : (x y x' y' : Int) → (x + y) + (x' + y') ≡ (x + x') + (y + y')
  lem x y x' y' =
       sym (+-assoc x y (x' + y'))
    ∙∙ cong (λ z → x + (y + z)) (+-comm x' y')
    ∙∙ cong (x +_) (+-assoc y y' x')
    ∙∙ cong (x +_) (+-comm (y + y') x')
    ∙∙ +-assoc x x' (y + y')

·-ldistr : (x y z : Int) → x · (y + z) ≡ ((x · y) + (x · z))
·-ldistr (pos zero) y z = refl
·-ldistr (pos (suc n)) y z =
     (λ i → (y + z) + (·-ldistr (pos n) y z i))
     ∙ lem y z (pos n · y) (pos n · z)
·-ldistr (negsuc zero) y z = sym (-distr y z)
·-ldistr (negsuc (suc n)) y z =
     (λ i → -distr y z (~ i) + ·-ldistr (negsuc n) y z i)
   ∙ lem (- y) (- z) (negsuc n · y) (negsuc n · z)

·-rdistr : (x y z : Int) → (y + z) · x ≡ ((y · x) + (z · x))
·-rdistr x y z = ·-comm (y + z) x ∙∙ ·-ldistr x y z ∙∙ cong₂ _+_ (·-comm x y) (·-comm x z)

decEqℕ : (x y : ℕ) → (x ≡ y) ⊎ (¬ x ≡ y)
decEqℕ zero zero = inl refl
decEqℕ zero (suc y) = inr λ p → snotz (sym p)
decEqℕ (suc x) zero = inr snotz
decEqℕ (suc x) (suc y) with decEqℕ x y
... | inl p = inl (cong suc p)
... | inr p = inr λ q → p (cong predℕ q)

decEqInt : (x y : Int) → (x ≡ y) ⊎ (¬ x ≡ y)
decEqInt (pos zero) (pos zero) = inl refl
decEqInt (pos zero) (pos (suc m)) = inr λ p → snotz (sym (injPos {a = zero} {b = suc m} p))
decEqInt (pos (suc n)) (pos zero) = inr λ p → snotz (injPos {a = suc n} {b = zero} p)
decEqInt (pos (suc n)) (pos (suc m)) with decEqInt (pos n) (pos m)
... | inl p = inl (cong pos (cong suc (injPos p)))
... | inr p = inr λ q → p (cong pos (cong predℕ (injPos q)))
decEqInt (pos n) (negsuc n₁) = inr λ p → negsucNotpos _ _ (sym p)
decEqInt (negsuc n) (pos n₁) = inr (negsucNotpos _ _)
decEqInt (negsuc n) (negsuc zero) = {!!}
decEqInt (negsuc zero) (negsuc (suc m)) = inr {!!}
decEqInt (negsuc (suc n)) (negsuc (suc m)) with decEqInt (negsuc n) (negsuc m)
... | inl p = {!!}
... | inr p = {!decEqℕ!}

x≡ : (n : ℕ) → (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] n ≡ (suc m))
x≡ zero = inl refl
x≡ (suc n) = inr (n , refl)

modh-type : ℕ → Int → Type₀
modh-type n z =
  Σ[ K ∈ (Int × ℕ) ]
      ((pos (snd K) < pos (suc n)))
    × (z ≡ (pos (snd K) + (fst K · pos (suc n))))

help1 : (n m : Int) → (predInt n · m) ≡ (n · m) - m
help1 (pos zero) (pos zero) = refl
help1 (pos zero) (pos (suc n)) = +-comm (negsuc n) 0
help1 (pos zero) (negsuc n) = cong sucInt (+-comm (pos n) 0)
help1 (pos (suc n)) m =
    sym (plusMinus m (pos n · m))
  ∙ cong (_- m) (+-comm (pos n · m) m)
help1 (negsuc n) m = +-comm (- m) (negsuc n · m) ∙ -≡+- (negsuc n · m) m

help : (n m : ℕ) (z : modh-type (suc n) (pos m))
     → (snd (fst z) ≡ (suc n)) ⊎ (¬ snd (fst z) ≡ (suc n))
     → modh-type (suc n) (pos (suc m))
fst (fst (help n m z (inl x))) = (fst (fst z)) + 1
snd (fst (help n m z (inl x))) = 0
fst (snd (help n m z (inl x))) = suc n , refl
snd (snd (help n m z (inl x))) =
     cong sucInt (snd (snd z))
  ∙∙ sucInt+ (pos (snd (fst z))) (fst (fst z) · pos (suc (suc n)))
  ∙∙ cong (_+ (fst (fst z) · pos (suc (suc n)))) (cong pos (cong suc x))
   ∙ +-comm (pos (2 +N n)) (fst (fst z) · pos (2 +N n))
  ∙∙ sym (·-rdistr (pos (2 +N n)) (fst (fst z)) 1)
  ∙∙ +-comm ((fst (fst z) + 1) · pos (2 +N n)) (pos 0)
fst (fst (help n m z (inr x))) = fst (fst z)
snd (fst (help n m z (inr x))) = suc (snd (fst z))
fst (snd (help n m z (inr x))) with x≡ (fst (fst (snd z)))
... | inr p = predℕ (fst (fst (snd z)))
            , ((cong (λ x → sucInt (pos (suc (predℕ x)) + pos (snd (fst z)))) (snd p))
           ∙∙ sucInt+ (pos (suc (fst p))) (pos (snd (fst z)))
           ∙∙ cong (λ x → pos (suc x) + pos (snd (fst z))) (sym (snd p))
            ∙ snd (fst (snd z)))
... | inl p =
      ⊥-rec (x (injPos (+-comm (pos (snd (fst z))) (pos 0)
                      ∙ cong (λ x → pos x + (pos (snd (fst z)))) (sym p)
                     ∙∙ sym (predInt+ (pos (suc (fst (fst (snd z))))) (pos (snd (fst z))))
                     ∙∙ cong predInt (fst (snd z) .snd))))
snd (snd (help n m z (inr x))) = cong sucInt (snd (snd z))
                               ∙ sucInt+ (pos (snd (fst z))) (fst (fst z) · pos (suc (suc n)))

pos+ : (n x : ℕ) → ℕ
pos+ zero x = 0
pos+ (suc n) x with (decEqℕ x n)
... | inl p = 0
... | inr p = suc x

negsuc++ : (n x : ℕ) → ℕ
negsuc++ zero x = 0
negsuc++ (suc n) x with decEqℕ x 0
... | inl p = n
... | inr p = x

_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
zero mod suc n = 0
suc x mod suc n = pos+ (suc n) (x mod (suc n))

_mod'_ : (z : Int) (n : ℕ) → ℕ
_mod'_ z zero = 0
_mod'_ (pos zero) (suc n) = 0
_mod'_ (pos (suc m)) (suc n) = pos+ (suc n) ((pos m) mod' (suc n))
_mod'_ (negsuc zero) (suc n) = n
_mod'_ (negsuc (suc m)) (suc n) = negsuc++ (suc n) ((negsuc m) mod' (suc n))

data ℤ'/ (n : ℕ) : Type₀ where
  [_] : ℕ → ℤ'/ n
  cyc : (x : ℕ) → [ x ] ≡ [ (x mod n)  ]

s : (n : ℕ) → ℤ'/ n → ℕ
s zero x = 0
s (suc n) [ x ] = x mod suc n
s (suc n) (cyc x i) = {!!}

hilfe : (n : ℕ) → (x : ℤ'/ n) → [ s n x ] ≡ x
hilfe zero x = {!!}
hilfe (suc n) [ x ] = sym (cyc x)
hilfe (suc n) (cyc x i) j =
  hcomp (λ k → λ {(i = i0) → cyc x (~ j ∨ ~ k)
                 ; (i = i1) → cyc (x mod suc n) (~ j)
                 ; (j = i0) → {!!} -- [ mod-mod n x i ]
                 ; (j = i1) → cyc x (i ∨ ~ k)})
        {!!}
{-
i = i0 ⊢ cyc x (~ j)
i = i1 ⊢ cyc (x mod suc n) (~ j)
j = i0 ⊢ [ mod-mod n x i ]
j = i1 ⊢ cyc x i
-}

test : (n : ℕ) → isSet (ℤ'/ n)
test n  =
  isOfHLevelRetract 2 (s n) [_] {!!} isSetℕ

isSetℤ' : (n : ℕ) → isSet (ℤ'/ n)
isSetℤ' zero = isProp→isSet {!!}
  where
  helper : isProp (ℤ'/ zero)
  helper [ x ] [ zero ] = cyc x
  helper [ x ] [ suc x₁ ] = cyc x ∙ sym (cyc (suc x₁))
  helper [ x ] (cyc zero i) = {!!}
  helper [ x ] (cyc (suc x₁) i) = {!!}
  helper (cyc x i) y = {!!}
isSetℤ' (suc n) = {!!}

contrZ/1 : isContr (ℤ'/ 1)
fst contrZ/1 = [ 1 ]
snd contrZ/1 [ zero ] = {!!}
snd contrZ/1 [ suc x ] = {!!} ∙ sym (cyc (suc x))
snd contrZ/1 (cyc x i) = {!!}

_+m_ : {n : ℕ} → ℕ → ℕ → ℕ
_+m_ {n = n} x y = {!x +N y!}

modh : (n : ℕ) (z : Int) →
  Σ[ K ∈ (Int × ℕ) ]
   ((pos (snd K) < pos (suc n)))
 × (z ≡ (pos (snd K) + (fst K · pos (suc n))))
modh zero z = (z , 0) , (((0 , refl) , λ i → +-comm (·-comm 1 z i) (pos 0) i))
modh (suc n) (pos zero) = (0 , 0) , (((suc n , refl) , refl))
fst (fst (modh (suc n) (pos (suc m)))) = fst (fst (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
snd (fst (modh (suc n) (pos (suc m)))) = snd (fst (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
fst (snd (modh (suc n) (pos (suc m)))) = fst (snd (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
snd (snd (modh (suc n) (pos (suc m)))) = snd (snd (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
modh (suc n) (negsuc zero) = {!!}
modh (suc n) (negsuc (suc m)) = help' n m (modh (suc n) (negsuc m)) (decEqℕ _ _)
  where
  help' : (n m : ℕ) (z : modh-type (suc n) (negsuc m))
       → (snd (fst z) ≡ 0) ⊎ (¬ snd (fst z) ≡ 0)
       → modh-type (suc n) (negsuc (suc m))
  fst (fst (help' n m z (inl x))) = fst (fst z) - 1
  snd (fst (help' n m z (inl x))) = suc n
  fst (snd (help' n m z (inl x))) = 0 , cong sucInt (+-comm 1 (pos n))
  snd (snd (help' n m z (inl x))) =
       cong predInt ((snd (snd z))
                 ∙∙ (cong (λ x → pos x + (fst (fst z) · pos (suc (suc n)))) x)
                 ∙∙ (+-comm (pos 0) (fst (fst z) · pos (suc (suc n)))))
    ∙∙ cong predInt (sym (minusPlus (pos (suc (suc n))) ((fst (fst z) · pos (suc (suc n))))))
    ∙∙ cong predInt (+-comm ((fst (fst z) · pos (suc (suc n))) - (pos (suc (suc n)))) (pos (suc (suc n))))
    ∙∙ predInt+ (pos (suc (suc n))) ((fst (fst z) · pos (suc (suc n))) - (pos (suc (suc n))))
    ∙∙ sym (cong (pos (suc n) +_) (help1 (fst (fst z)) (pos (suc (suc n)))))
  help' n m z (inr x) = {!!}



-- mod_ : (n : ℕ) → ℕ →  ℕ
-- (mod zero) m = 0
-- (mod suc zero) zero = 0
-- (mod suc zero) (suc zero) = 1
-- (mod suc zero) (suc (suc m)) = (mod suc zero) m
-- (mod suc (suc n)) m = {!eq/ !}

-- intAdd : (n : ℕ) → ℕ →  ℕ → ℕ
-- intAdd zero _ _ = zero
-- intAdd (suc zero) zero k = k
-- intAdd (suc zero) (suc zero) zero = 1
-- intAdd (suc zero) (suc (suc m)) zero = intAdd (suc zero) m zero
-- intAdd (suc zero) (suc m) (suc k) = intAdd (suc zero) m k
-- intAdd (suc (suc n)) m k with discreteℕ (intAdd (suc n) m k) n
-- ... | yes p = {!!}
-- ... | no p = {!!}

-- _divides_ : (x y : Int) → Type₀
-- _divides_ x y = Σ[ k ∈ Int ] k · x ≡ y

-- dec-divides' : (x y : Int) → Dec (x divides y)
-- dec-divides' (pos zero) (pos zero) = yes (0 , refl)
-- dec-divides' (pos zero) (pos (suc n)) = no λ {(x , p) → {!!}}
-- dec-divides' (pos zero) (negsuc n) = no {!!}
-- dec-divides' (pos (suc zero)) y = yes (y , {!refl!})
-- dec-divides' (pos (suc (suc n))) (pos zero) = yes (0 , refl)
-- dec-divides' (pos (suc (suc n))) (pos (suc m)) with (dec-divides' (pos (2 +N n)) (pos m))
-- ... | yes (x , k) = no λ {(x2 , k2) → {!!}}
-- ... | no p = yes ({!p!} , {!!})
-- dec-divides' (pos (suc (suc n))) (negsuc n₁) = {!!}
-- dec-divides' (negsuc zero) y = yes (- y , {!!})
-- dec-divides' (negsuc (suc n)) (pos zero) = yes (0 , refl)
-- dec-divides' (negsuc (suc n)) (pos (suc m)) = {!!}
-- dec-divides' (negsuc (suc n)) (negsuc m) = {!!}

-- infixl 30 _,_
-- infixl 50 ⋆,_
-- infixr 50 ∣_

-- finVec : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
-- finVec {ℓ} zero A = finVec0
--   module _ where
--   data finVec0 : Type ℓ where
--     ∣_ : A → finVec0 
-- finVec {ℓ} (suc n) A = finVec>0
--   module _ where
--   data finVec>0 : Type ℓ where
--     _,_ : finVec n A → A → finVec>0

-- s : finVec 3 Int
-- s = (((∣ 1) , 3) , 5) , 3

-- +finVec : ∀ {ℓ} {A : Type ℓ} (+A : A → A → A) (n : ℕ) (x y : finVec n A) → finVec n A
-- +finVec _+A_ zero (∣ x) (∣ y) = ∣ (x +A y)
-- +finVec _+A_ (suc n) (x , x2) (y , y2) = +finVec _+A_ n x y , (x2 +A y2)

-- data transposeVec {ℓ} (n : ℕ) (A : Type ℓ) : Type ℓ where
--   [_]ᵗ : finVec n A → transposeVec n A

-- _×_-matrix : ∀ {ℓ} → (n m : ℕ) → Type ℓ → Type ℓ
-- _×_-matrix {ℓ} zero m A = Unit*
-- _×_-matrix {ℓ} (suc n) zero A = Unit*
-- _×_-matrix {ℓ} (suc zero) (suc m) A =
--   transposeVec m A
-- _×_-matrix {ℓ} (suc (suc n)) (suc zero) A =
--   finVec (suc n) A
-- _×_-matrix {ℓ} (suc (suc n)) (suc (suc m)) A =
--   transposeVec (suc n) (finVec (suc m) A)

-- test : (2 × 2 -matrix) Int
-- test =
--   [ (∣ ((∣ 1) , 2))
--     , ((∣ 3) , 4) ]ᵗ

-- _ᵗ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → finVec n A → transposeVec n A
-- x ᵗ = [ x ]ᵗ

-- _ᵗ⁻ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → transposeVec n A → finVec n A 
-- ([ x ]ᵗ) ᵗ⁻ = x

-- vecProd : ∀ {ℓ} {A : Type ℓ} {n  : ℕ} (∙A : A → A → A) → finVec n A → transposeVec n A → finVec n A
-- vecProd {n = zero} _∙A_ (∣ x) [ ∣ y ]ᵗ = ∣ (x ∙A y) -- x ∙A y
-- vecProd {n = suc n} _∙A_ (x , tx) [ y , ty ]ᵗ = (vecProd _∙A_ x [ y ]ᵗ) , (tx ∙A ty) -- vecProd _+A_ _∙A_ x [ y ]ᵗ +A (tx +A ty)

-- scalarVec : ∀ {ℓ} {A : Type ℓ} {n  : ℕ} (+A ·A : A → A → A) (x : A) → finVec n A
-- scalarVec {n = zero} +A _∙A_ x = ∣ x
-- scalarVec {n = suc n} +A _∙A_ x = scalarVec +A _∙A_ x , x


-- matr-mult : ∀ {ℓ} {A : Type ℓ} (n m l : ℕ)
--                   (+A ·A : A → A → A)
--                   (M : ((suc n) × (suc m) -matrix) A)
--                → ((suc m) × (suc l) -matrix) A → ((suc n) × (suc l) -matrix) A
-- matr-mult zero zero l _+A_ _∙A_ [ ∣ x ]ᵗ y = [ vecProd _∙A_ (scalarVec _+A_ _∙A_ x) y ]ᵗ
-- matr-mult zero (suc m) l _+A_ _·_ [ x ]ᵗ S = {!S!}
-- matr-mult (suc n) m l _+A_ _·_ M S = {!!}

-- matr : ∀ {ℓ} → ℕ → ℕ → Type ℓ → Type ℓ
-- matr zero y A = {!!}
-- matr {ℓ} (suc n) y A = {!!}

-- kalaha : ℕ → Type₀
-- kalaha zero = Unit
-- kalaha (suc n) = T
--   module _ where
--   data T : Type₀ where
--     [_] : kalaha n → T
--     +1 : T
-- open import Cubical.HITs.S1
-- data S¹-mod (n : ℕ) : Type₀ where
--   [_] : S¹ → S¹-mod n
--   coher : cong [_] (intLoop (pos n)) ≡ refl

-- 0k : {n : ℕ} → kalaha n
-- 0k {n = zero} = tt
-- 0k {n = suc n} = [ 0k ]

-- upBack : (n : ℕ) → kalaha n →  kalaha (suc n)
-- upBack zero = [_]
-- upBack (suc n) = [_]

-- downUnder : (n : ℕ) → kalaha (suc n) → kalaha n
-- downUnder zero x = _
-- downUnder (suc n) [ x ] = x
-- downUnder (suc n) +1 = 0k
-- open import Cubical.Data.Empty renaming (rec to ⊥-rec)
-- ≠-fib : (n : ℕ) → kalaha (suc n) → Type₀
-- ≠-fib n [ x ] = Unit
-- ≠-fib n +1 = ⊥
-- open import Cubical.Data.Unit
-- +1≠[] : {n : ℕ} {x : kalaha n} → ¬ (+1 ≡ [ x ])
-- +1≠[] {n = n} p = transport (cong (≠-fib n) (sym p)) tt

-- upBck-downUnder : (n : ℕ) (x : _) → Σ[ y ∈ kalaha n ] x ≡ [ y ] → upBack n (downUnder n x) ≡ x
-- upBck-downUnder zero [ x ] _ = refl
-- upBck-downUnder (suc n) [ x ] _ = refl
-- upBck-downUnder zero +1 (y , p) = ⊥-rec (+1≠[] p)
-- upBck-downUnder (suc n) +1 (y , p) = ⊥-rec (+1≠[] p)

-- revFun : (n : ℕ) → (x y : kalaha n) → Path (T n) [ x ] [ y ] → x ≡ y
-- revFun zero x y _ = refl
-- revFun (suc n) x y = cong (downUnder (suc n))

-- jaha : (n : ℕ) (x : kalaha (suc n)) (p1 : _) (p2 : _) → refl  ≡ upBck-downUnder n x p1 ∙∙ refl ∙∙ sym (upBck-downUnder n x p2)
-- jaha zero [ x ] (x' , p1) (y' , p2) = rUnit refl
-- jaha (suc n) [ x ] (x' , p1) (y' , p2) = rUnit refl
-- jaha zero +1 (x' , p1) (y' , p2) = ⊥-rec (+1≠[] p1)
-- jaha (suc n) +1 (x' , p1) (y' , p2) = ⊥-rec (+1≠[] p1)

-- retra : (n : ℕ) (x y : kalaha (suc n)) (p : x ≡ y) (p1 : Σ[ a ∈ kalaha n ] x ≡ [ a ]) (p2 : Σ[ b ∈ kalaha n ] y ≡ [ b ])
--       → cong (upBack n) (cong (downUnder n) p) ≡ (upBck-downUnder n x p1  ∙∙ p ∙∙ sym (upBck-downUnder n y p2))
-- retra n x y =
--   J (λ y p → (p1 : Σ[ a ∈ kalaha n ] x ≡ [ a ]) (p2 : Σ[ b ∈ kalaha n ] y ≡ [ b ])
--            → cong (upBack n) (cong (downUnder n) p) ≡ (upBck-downUnder n x p1  ∙∙ p ∙∙ sym (upBck-downUnder n y p2)))
--     (jaha n x)

-- pathSpaceIso : (n : ℕ) (x y : kalaha n)
--             → Iso (x ≡ y) (Path (kalaha (suc n)) [ x ] [ y ])
-- Iso.fun (pathSpaceIso n x y) p = cong [_] p
-- Iso.inv (pathSpaceIso n x y) = revFun n _ _
-- Iso.rightInv (pathSpaceIso zero x y) p =
--     retra 0 [ x ] [ y ] p (_ , refl) (_ , refl)
--   ∙ sym (rUnit p)
-- Iso.rightInv (pathSpaceIso (suc n) x y) p =
--     retra (suc n) [ x ] [ y ] p (_ , refl) (_ , refl)
--   ∙ sym (rUnit p)
-- Iso.leftInv (pathSpaceIso zero x y) _ = isSetUnit _ _ _ _
-- Iso.leftInv (pathSpaceIso (suc n) x y) =
--   J (λ y p → revFun (suc n) _ _ (cong [_] p) ≡ p) refl

-- decKalaha : (n : ℕ) → Discrete (kalaha n)
-- decKalaha zero _ _ = yes refl
-- decKalaha (suc n) [ x ] [ y ] =
--   transport (λ i → Dec (isoToPath (pathSpaceIso n x y) i)) (decKalaha n x y)
-- decKalaha (suc n) [ x ] +1 = no λ p → ⊥-rec (+1≠[] (sym p))
-- decKalaha (suc n) +1 [ x ] = no λ p → ⊥-rec (+1≠[] p)
-- decKalaha (suc n) +1 +1 = yes refl

-- isSetKalaha : (n : ℕ) → isSet (kalaha n)
-- isSetKalaha n = Discrete→isSet (decKalaha n)

-- repr : {n : ℕ} → kalaha n → ℕ
-- repr {n = zero} x = 0
-- repr {n = suc n} [ x ] = repr x
-- repr {n = suc n} +1 = (suc n)

-- _++1 : {n : ℕ}(x : kalaha n) → kalaha n
-- _++1 {n = zero} x = tt
-- _++1 {n = suc zero} [ x ] = +1
-- _++1 {n = suc zero} +1 = [ tt ]
-- _++1 {n = suc (suc n)} [ [ x ] ] = [ [ x ] ++1 ]
-- _++1 {n = suc (suc n)} [ +1 ] = +1
-- _++1 {n = suc (suc n)} +1 = 0k

-- comp^_ : ∀ {ℓ} {A : Type ℓ} → ℕ → (f : A → A) → A → A
-- (comp^ zero) f x = x
-- (comp^ (suc n)) f = f ∘ (comp^ n) f

-- comp'^_ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → kalaha n → (f : A → A) → A → A
-- comp'^_ {n = zero} x f a = a
-- comp'^_ {n = suc zero} [ x ] f a = a
-- comp'^_ {n = suc zero} +1 f = f
-- comp'^_ {n = suc (suc n)} [ x ] f = comp'^_ {n = (suc n)} x f
-- comp'^_ {n = suc (suc zero)} +1 f = f ∘ f
-- comp'^_ {n = suc (suc (suc n))} +1 f =
--   f ∘ comp'^_ {n = (suc (suc n))} [ +1 ] f
--  --f ∘ (comp'^_ {n = suc n} [ {!!} ]) {!f!}

-- data finℤ (n : ℕ) : Type₀ where
--   [_] : ℕ → finℤ n
--   p : 

-- _+k_ : {n : ℕ} → kalaha n → kalaha n → kalaha n
-- _+k_ {n = zero} x y = x
-- _+k_ {n = suc zero} x y = {!!}
-- _+k_ {n = suc (suc n)} [ [ x ] ] [ [ y ] ] = {!!}
-- _+k_ {n = suc (suc n)} [ [ x ] ] [ +1 ] = {!!}
-- _+k_ {n = suc (suc n)} [ +1 ] [ x₁ ] = {!!}
-- _+k_ {n = suc (suc n)} [ x ] +1 = {!!}
-- _+k_ {n = suc (suc n)} +1 y = {!!}
-- -- (comp'^ y) _++1 x

-- -- _1-- : {n : ℕ}(x : kalaha n) → kalaha n
-- -- _1-- {n = n} x = (comp^ n) _++1 x

-- -- _-k_ : {n : ℕ} → kalaha n → kalaha n → kalaha n
-- -- _-k_ {n = n} x y = (comp'^ y) _1-- x

-- -- c : kalaha 3
-- -- c = +1 +k +1

-- -- comp^-helper' : {n : ℕ} (x : kalaha (2 +N n)) (y : kalaha n) → (comp^ repr x) (_++1 {n = (2 +N n)}) [ [ y ] ] ≡ (({![ (comp^ repr x) (_++1 {n = (1 +N n)}) [ y ] ] !} ++1) ++1)
-- -- comp^-helper' {n = zero} [ [ x ] ] y = refl
-- -- comp^-helper' {n = zero} [ +1 ] y = refl
-- -- comp^-helper' {n = suc n} [ x ] y = {!!}
-- -- comp^-helper' {n = zero} +1 y = {!refl!}
-- -- comp^-helper' {n = suc n} +1 y = {!refl!}


-- -- open import Cubical.Data.Sum
-- -- comp^-helper : {n : ℕ} (x y : kalaha n) → (comp'^ y) _++1 x ≡ (comp'^ x) _++1 y
-- -- comp^-helper {n = zero} x y = refl
-- -- comp^-helper {n = suc zero} [ x ] [ x₁ ] = refl
-- -- comp^-helper {n = suc zero} [ x ] +1 = refl
-- -- comp^-helper {n = suc zero} +1 [ x ] = refl
-- -- comp^-helper {n = suc zero} +1 +1 = refl
-- -- comp^-helper {n = suc (suc n)} [ x ] [ y ] = {!y!}
-- --   where
  
-- --   help : {n : ℕ} (x : _) (y : _) → ((comp'^ y) (_++1 {n = suc (suc n)}) [ x ] ≡ [ (comp'^_ {n = (suc n)} y) (_++1 {n = suc n}) x ])
-- --       ⊎ ((comp'^ y) (_++1 {n = suc (suc n)}) [ x ] ≡ +1)
-- --   help {n = zero} [ x ] [ x₁ ] = inl refl
-- --   help {n = zero} [ x ] +1 = inl refl
-- --   help {n = zero} +1 [ x ] = inl refl
-- --   help {n = zero} +1 +1 = inr refl
-- --   help {n = suc n} [ x ] [ y ] with (help x y)
-- --   ... | inr p = inl ({!p!} ∙∙ {!!} ∙∙ λ i → [ p (~ i) ])
-- --   ... | inl p = {!p!}
-- --   help {n = suc n} [ x ] +1 = {!!}
-- --   help {n = suc n} +1 y = {!!}
-- -- comp^-helper {n = suc (suc n)} [ x ] +1 = {!!}
-- -- comp^-helper {n = suc (suc n)} +1 y = {!!}


-- -- _∙k_ : {n : ℕ} → kalaha n → kalaha n → kalaha n
-- -- _∙k_ {n = zero} = λ _ _ → tt
-- -- _∙k_ {n = suc n} x y = (comp^ repr y) (λ y → x +k y) y

-- -- +k-comm : {n : ℕ} → (x y : kalaha n) → x +k y ≡ y +k x
-- -- +k-comm {n = zero} x y = refl
-- -- +k-comm {n = suc zero} [ x ] [ x₁ ] = refl
-- -- +k-comm {n = suc zero} [ x ] +1 = refl
-- -- +k-comm {n = suc zero} +1 [ x ] = refl
-- -- +k-comm {n = suc zero} +1 +1 = refl
-- -- +k-comm {n = suc (suc n)} [ x ] [ y ] = {!!}
-- -- +k-comm {n = suc (suc n)} [ x ] +1 = {!!}
-- -- +k-comm {n = suc (suc n)} +1 y = {!!}


-- -- help : (n : ℕ) → kalaha n → Int
-- -- help zero x = 0
-- -- help (suc n) [ x ] = help n x
-- -- help (suc n) +1 = pos (suc n)

-- -- isSet-kalaha : ℕ → Type₀
-- -- isSet-kalaha = {!!}

-- -- dec-divides : (x y : Int) → Dec (x divides y)
-- -- dec-divides (pos zero) (pos zero) = yes (0 , refl)
-- -- dec-divides (pos (suc n)) (pos zero) = yes (0 , refl)
-- -- dec-divides (pos zero) (pos (suc m)) = {!!}
-- -- dec-divides (pos (suc n)) (pos (suc m)) with (dec-divides (pos (suc n)) (pos m))
-- -- ... | yes (x , k) = yes {!!}
-- -- ... | no p = {!!}
-- -- dec-divides (pos n) (negsuc n₁) = {!!}
-- -- dec-divides (negsuc n) y = {!!}

-- -- ℤ/→ℤ/' : (n : ℕ) → ℤ/ n → ℤ/' n
-- -- ℤ/→ℤ/' n [ x ] = [ x ]
-- -- ℤ/→ℤ/' n (kill-l x i) = (eq/ x (pos n + x) refl) (~ i)

-- -- ℤ/'ℤ : (n : ℕ) → Int
-- -- ℤ/'ℤ n = {!!}

-- -- -- ℤ/_ : (n : ℕ) → Type₀
-- -- -- ℤ/ n = Pushout (add n) (idfun _)

-- -- -- ℤ/→ℕ : (n : ℕ) → ℤ/ n → Int
-- -- -- ℤ/→ℕ n (inl x) = pos x - pos n
-- -- -- ℤ/→ℕ n (inr x) = pos x
-- -- -- ℤ/→ℕ n (push a i) = pos- n a i

-- -- -- ℕ→ℤ/ : (n : ℕ) → Int → ℤ/ n
-- -- -- ℕ→ℤ/ n (pos m) = inr m
-- -- -- ℕ→ℤ/ n (negsuc m) = inr m

-- -- -- toPropElim : ∀ {ℓ} (n : ℕ) → {A : ℤ/ n → Type ℓ}
-- -- --      → ((x : _) → isProp (A x))
-- -- --      → ((n : ℕ) → A (inl n))
-- -- --      → (x : _) → A x
-- -- -- toPropElim n prop f (inl x) = f x
-- -- -- toPropElim n {A = A} prop f (inr x) = transport (cong A (push x)) (f (n + x))
-- -- -- toPropElim n {A = A} prop f (push a i) =
-- -- --   isProp→PathP {B = λ i → A (push a i)} (λ _ → prop _)
-- -- --                 (f (n + a)) (transport (cong A (push a)) (f (n + a))) i 

-- -- -- open import Cubical.Relation.Nullary

-- -- -- decEqℤ/ : (n : ℕ) → Discrete (ℤ/ n)
-- -- -- decEqℤ/ n =
-- -- --   toPropElim n (λ _ → isPropΠ λ _ → isPropDec {!!}) {!!}

-- -- -- -+hom : (x n : _) → ℕ→ℤ/ (suc n) (pos x +negsuc n) ≡ inr x
-- -- -- -+hom x n = {!!}

-- -- -- -hom : (x n : _) → ℕ→ℤ/ n (pos x - pos n) ≡ ℕ→ℤ/ n (pos x)
-- -- -- -hom x zero = refl
-- -- -- -hom x (suc n) = -+hom x n

-- -- -- q : (x n : _) → Path (ℤ/ n) (inl ((add n) x)) (inl x)
-- -- -- q x zero = refl
-- -- -- q x (suc n) = {!!}

-- -- -- p : (x n : _) → ℕ→ℤ/ n (pos x - pos n) ≡ inl x
-- -- -- p x n = -hom x n ∙∙ sym (push x) ∙∙ {!!}

-- -- -- test : (n : ℕ) → (x : ℤ/ n) → ℕ→ℤ/ n (ℤ/→ℕ n x) ≡ x
-- -- -- test n (inl x) = p x n
-- -- -- test n (inr x) =
-- -- --   transport (λ i → ℕ→ℤ/ n (pos- n x i) ≡ push x i) (p ((add n) x) n)
-- -- -- test n (push x i) j =
-- -- --   transp (λ z → ℕ→ℤ/ n (pos- n x (i ∧ z)) ≡ push x (i ∧ z)) (~ i) (p ((add n) x) n) j

-- -- -- isSet-ℤ/ : (n : ℕ) → isSet (ℤ/ n)
-- -- -- isSet-ℤ/ n =
-- -- --   isSetRetract (ℤ/→ℕ n)
-- -- --                (ℕ→ℤ/ n)
-- -- --                (test n)
-- -- --                isSetInt

-- -- -- -- S : ℕ₋₁ → Type₀
-- -- -- -- S neg1 = ⊥
-- -- -- -- S (ℕ→ℕ₋₁ n) = Susp (S (-1+ n))

-- -- -- -- S₊ : ℕ → Type₀
-- -- -- -- S₊ 0 = Bool
-- -- -- -- S₊ 1 = S¹
-- -- -- -- S₊ (suc (suc n)) = Susp (S₊ (suc n))

-- -- -- -- ptSn : (n : ℕ) → S₊ n
-- -- -- -- ptSn zero = true
-- -- -- -- ptSn (suc zero) = base
-- -- -- -- ptSn (suc (suc n)) = north

-- -- -- -- -- Pointed version
-- -- -- -- S₊∙ : (n : ℕ) → Pointed₀
-- -- -- -- S₊∙ n = (S₊ n) , ptSn n
