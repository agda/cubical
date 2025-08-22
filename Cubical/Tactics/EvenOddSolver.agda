{-# OPTIONS --safe #-}
{-

This module defines a rather primitive solver for the evenness of
expressions over ℕ.

Input: Expression s over ℕ, a list of assignments v : Vec ((x : ℕ) × even? x) n
Output: Proof that ⟦ s ⟧ v is even/odd, if possible to determine.

-}
module Cubical.Tactics.EvenOddSolver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData hiding (snotz)
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (zero-≤ ; isProp≤)
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Vec.Base
open import Cubical.Data.Bool hiding (isProp≤)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ renaming (map to ⊎map)
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Fin as ΣFin hiding (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.List as L hiding (map) renaming (_++_ to _＋_)
open import Cubical.Data.Unit

open import Cubical.Tactics.NatSolver.NatExpression

open Eval

private
  variable
    ℓ ℓ' ℓ'' : Level

data even? (n : ℕ) : Type where
  ？ : even? n
  yup : isEvenT n → even? n
  nope : isOddT n → even? n

-- First step: given a vector of naturals equipped with information
-- about whether or not they are even, return a new vector with each
-- even replaced by 0 and each odd replaced by 1.
evenOddVecLen : {n : ℕ}
  → Vec (Σ[ k ∈ ℕ ] (even? k)) n → ℕ
evenOddVecLen [] = 0
evenOddVecLen ((s , ？) ∷ xs) = suc (evenOddVecLen xs)
evenOddVecLen ((s , yup x) ∷ xs) = evenOddVecLen xs
evenOddVecLen ((s , nope x) ∷ xs) = evenOddVecLen xs

filterEvenOddVec : {n : ℕ}
  (t : Vec (Σ[ x ∈ ℕ ] (even? x)) n)
  → Vec ℕ (evenOddVecLen t)
filterEvenOddVec [] = []
filterEvenOddVec ((x , ？) ∷ t) = x ∷ filterEvenOddVec t
filterEvenOddVec ((x , yup s) ∷ t) = filterEvenOddVec t
filterEvenOddVec ((x , nope s) ∷ t) = filterEvenOddVec t

-- Now do the same things for expressions over ℕ
filterEvenOddExpr : {n : ℕ} (s : Expr n)
  (t : Vec (Σ[ x ∈ ℕ ] (even? x)) n)
  → Expr (evenOddVecLen t)
filterEvenOddExpr (K k) t = K k
filterEvenOddExpr (∣ zero) ((_ , ？) ∷ t) = ∣ zero
filterEvenOddExpr (∣ (suc k)) ((_ , ？) ∷ t) = Expr↑ (filterEvenOddExpr (∣ k) t)
filterEvenOddExpr (∣ zero) ((_ , yup ev) ∷ t) = K 0
filterEvenOddExpr (∣ (suc k)) ((_ , yup s) ∷ t) = filterEvenOddExpr (∣ k) t
filterEvenOddExpr (∣ (suc k)) ((_ , nope s) ∷ t) = filterEvenOddExpr (∣ k) t
filterEvenOddExpr (∣ zero) ((_ , nope od) ∷ t) = K 1
filterEvenOddExpr (s +' s₁) t = filterEvenOddExpr s t +' filterEvenOddExpr s₁ t
filterEvenOddExpr (s ·' s₁) t = filterEvenOddExpr s t ·' filterEvenOddExpr s₁ t

-- Key lemma: the evaluation of a given expression mod 2 is invariant
-- w.r.t. this kind of replacement
evalFilterEvenOdd : {n : ℕ} (s : Expr n)
  (t : Vec (Σ[ x ∈ ℕ ] (even? x)) n)
  → (⟦ s ⟧ (map fst t)) mod 2
  ≡ (⟦ filterEvenOddExpr s t ⟧ (filterEvenOddVec t)) mod 2
evalFilterEvenOdd (K x) t = refl
evalFilterEvenOdd (∣ zero) ((s , ？) ∷ t) = refl
evalFilterEvenOdd (∣ zero) ((s , yup x) ∷ t) = isEvenT↔≡0 s .fst x
evalFilterEvenOdd (∣ zero) ((s , nope x) ∷ t) = isOddT↔≡1 s .fst x
evalFilterEvenOdd (∣ (suc k)) ((s , ？) ∷ t) =
  evalFilterEvenOdd (∣ k) t
  ∙ sym (cong (_mod 2) (Expr↑ForgetFirst
    (filterEvenOddExpr (∣ k) t) s (filterEvenOddVec t)))
  where
  Expr↑ForgetFirst : {n : ℕ} (x : Expr n) (s : ℕ) (w : _)
    → ⟦ Expr↑ x ⟧ (s ∷ w) ≡ ⟦ x ⟧ w
  Expr↑ForgetFirst (K x) s w = refl
  Expr↑ForgetFirst (∣ x) s w = refl
  Expr↑ForgetFirst (x +' x₁) s w =
    cong₂ _+_ (Expr↑ForgetFirst x s w) (Expr↑ForgetFirst x₁ s w)
  Expr↑ForgetFirst (x ·' x₁) s w =
    cong₂ _·_ (Expr↑ForgetFirst x s w) (Expr↑ForgetFirst x₁ s w)
evalFilterEvenOdd (∣ (suc x)) ((s , yup _) ∷ t) = evalFilterEvenOdd (∣ x) t
evalFilterEvenOdd (∣ (suc x)) ((s , nope _) ∷ t) = evalFilterEvenOdd (∣ x) t
evalFilterEvenOdd (s +' s₁) t =
    mod+mod≡mod 2 (⟦ s ⟧ (map fst t)) (⟦ s₁ ⟧ (map fst t))
  ∙ cong₂ (λ x y → (x + y) mod 2)
          (evalFilterEvenOdd s t) (evalFilterEvenOdd s₁ t)
  ∙ sym (mod+mod≡mod 2 (⟦ filterEvenOddExpr s t ⟧ (filterEvenOddVec t))
                       (⟦ filterEvenOddExpr s₁ t ⟧ (filterEvenOddVec t)))
evalFilterEvenOdd (s ·' s₁) t =
    mod·mod≡mod 2 (⟦ s ⟧ (map fst t)) (⟦ s₁ ⟧ (map fst t))
  ∙ cong₂ (λ x y → (x · y) mod 2)
          (evalFilterEvenOdd s t) (evalFilterEvenOdd s₁ t)
  ∙ sym (mod·mod≡mod 2 (⟦ filterEvenOddExpr s t ⟧ (filterEvenOddVec t))
                       (⟦ filterEvenOddExpr s₁ t ⟧ (filterEvenOddVec t)))

-- evaluating mod 2 in different orders
evalMod2 : {n : ℕ} (s : Expr n) (t : Vec ℕ n)
  → (⟦ s ⟧ t) mod 2 ≡ (⟦ s ⟧ (map (_mod 2) t)) mod 2
evalMod2 (K x) t = refl
evalMod2 (∣ zero) (s ∷ xs) = sym (mod-idempotent s)
evalMod2 (∣ (suc x)) (s ∷ xs) = evalMod2 (∣ x) xs
evalMod2 (s +' s₁) t =
  mod+mod≡mod 2 (⟦ s ⟧ t) (⟦ s₁ ⟧ t)
  ∙ cong₂ (λ x y → (x + y) mod 2) (evalMod2 s t) (evalMod2 s₁ t)
  ∙ sym (mod+mod≡mod 2 (⟦ s ⟧ (map (_mod 2) t)) (⟦ s₁ ⟧ (map (_mod 2) t)))
evalMod2 (s ·' s₁) t =
  mod·mod≡mod 2 (⟦ s ⟧ t) (⟦ s₁ ⟧ t)
  ∙ cong₂ (λ x y → (x · y) mod 2) (evalMod2 s t) (evalMod2 s₁ t)
  ∙ sym (mod·mod≡mod 2 (⟦ s ⟧ (map (_mod 2) t)) (⟦ s₁ ⟧ (map (_mod 2) t)))

-- Step 2: characterise dependent types over Vec (Fin 2) n
Fin2Lists : (n : ℕ) → List (Vec (ΣFin.Fin 2) n)
Fin2Lists zero = [ [] ]
Fin2Lists (suc n) = L.map (0 ∷_) (Fin2Lists n)
                  ＋ L.map (1 ∷_) (Fin2Lists n)

ListFinIndT : (n : ℕ) (A : Vec (ΣFin.Fin 2) n → Type)
  → List (Vec (ΣFin.Fin 2) n) → Type
ListFinIndT n A [] = Unit
ListFinIndT n A (x ∷ xs) = A x × ListFinIndT n A xs

ListFinIndT++ : {n : ℕ} (A : Vec (ΣFin.Fin 2) n → Type)
  (xs ys : List (Vec (ΣFin.Fin 2) n))
  → ListFinIndT n A (xs ＋ ys)
  → ListFinIndT n A xs × ListFinIndT n A ys
ListFinIndT++ A [] ys t = tt , t
ListFinIndT++ {n = n} A (x ∷ xs) ys (t , v) .fst .fst = t
ListFinIndT++ {n = n} A (x ∷ xs) ys (t , v) .fst .snd =
  fst (ListFinIndT++ A xs ys v)
ListFinIndT++ {n = n} A (x ∷ xs) ys (t , v) .snd =
  snd (ListFinIndT++ A xs ys v)

-- Key result:
ListFinInd : (n : ℕ) {A : Vec (ΣFin.Fin 2) n → Type}
  → ListFinIndT n A (Fin2Lists n)
  → (x : _) → A x
ListFinInd n {A = A} ind [] = ind .fst
ListFinInd (suc n) {A = A} ind (s ∷ w) with
  (ListFinIndT++ A (L.map (0 ∷_) (Fin2Lists n))
                   (L.map (1 ∷_) (Fin2Lists n)) ind)
... | le , ri = transport refl
  (ListFinInd n {A = λ x → A (s ∷ x)}
    (transport (ListFinIndT↓ n A (Fin2Lists n) s)
      (lem s)) w)
    where
    ListFinIndT↓ : (n : ℕ) (A : Vec (ΣFin.Fin 2) (suc n) → Type)
      (l : List (Vec (ΣFin.Fin 2) n)) (x : ΣFin.Fin 2)
      → ListFinIndT (suc n) A (L.map (x ∷_) l)
       ≡ ListFinIndT n (λ y → A (x ∷ y)) l
    ListFinIndT↓ n A [] x = refl
    ListFinIndT↓ n A (y ∷ l) x = cong₂ _×_ refl (ListFinIndT↓ n A l x)

    lem : (s : _) → ListFinIndT (suc n) A (L.map (_∷_ s) (Fin2Lists n))
    lem (zero , t) =
      subst (λ t → ListFinIndT (suc n) A (L.map (_∷_ (zero , t))
                     (Fin2Lists n)))
            (isProp≤ (1 , (λ i → 2)) t) le
    lem (one , t) =
      subst (λ t → ListFinIndT (suc n) A (L.map (_∷_ (one , t))
                     (Fin2Lists n)))
            (isProp≤ (0 , (λ i → 2)) t) ri
    lem (suc (suc s) , t) =
      ⊥.rec (snotz (cong predℕ
              (cong predℕ (+-comm (3 + s) (t .fst) ∙ snd t))))

private
  ℕPath : (n m : ℕ) → Type
  ℕPath zero zero = Unit
  ℕPath zero (suc m) = ⊥
  ℕPath (suc n) zero = ⊥
  ℕPath (suc n) (suc m) = ℕPath n m

  ℕPath→≡ : {n m : ℕ} → ℕPath n m → n ≡ m
  ℕPath→≡ {n = zero} {zero} p = refl
  ℕPath→≡ {n = suc n} {suc m} p = cong suc (ℕPath→≡ {n = n} {m} p)

  ℕ→Fin2 : ℕ → ΣFin.Fin 2
  ℕ→Fin2 n .fst = n mod 2
  ℕ→Fin2 n .snd = mod< one n

-- main result
module _ {n : ℕ} (s : Expr n) (x : ℕ)
  (t : Vec (Σ[ k ∈ ℕ ] (even? k)) n)
  {u : ListFinIndT (evenOddVecLen t)
      (λ v → ℕPath (⟦ filterEvenOddExpr s t ⟧ (map fst v) mod two) (x mod two))
                    (Fin2Lists (evenOddVecLen t))} where
  -- The complicated type of u reduces to Unit × ... × Unit if the
  -- input expression indeed is even (which Agda can fill automatically)

  solveWithConstraints : (⟦ s ⟧ (map fst t)) mod two ≡ x mod two
  solveWithConstraints =
      evalFilterEvenOdd s t
    ∙ evalMod2 (filterEvenOddExpr s t) (filterEvenOddVec t)
    ∙ ℕPath→≡ (subst (λ a → ℕPath (a mod two) (x mod two)) lem main)
    where
    lem : ⟦ filterEvenOddExpr s t ⟧ (map fst (map ℕ→Fin2 (filterEvenOddVec t)))
        ≡ ((⟦ filterEvenOddExpr s t ⟧ (map (_mod two) (filterEvenOddVec t))))
    lem = cong (⟦ filterEvenOddExpr s t ⟧)
        (sym (compMap fst ℕ→Fin2 (filterEvenOddVec t)))

    main = ListFinInd (evenOddVecLen t)
             {A = λ v → ℕPath (⟦ filterEvenOddExpr s t ⟧
                                    (map fst v) mod two)
                               (x mod two)}
             u (map ℕ→Fin2 (filterEvenOddVec t))

solveIsEven : {n : ℕ} (s : Expr n)
  (t : Vec (Σ[ k ∈ ℕ ] (even? k)) n)
  {u : ListFinIndT (evenOddVecLen t)
      (λ v → ℕPath (⟦ filterEvenOddExpr s t ⟧ (map fst v) mod two) 0)
                    (Fin2Lists (evenOddVecLen t))}
   → isEvenT (⟦ s ⟧ (map fst t))
solveIsEven s t {u = u} =
  isEvenT↔≡0 (⟦ s ⟧ (map fst t)) .snd
    (solveWithConstraints s 0 t {u})

solveIsOdd : {n : ℕ} (s : Expr n)
  (t : Vec (Σ[ k ∈ ℕ ] (even? k)) n)
  {u : ListFinIndT (evenOddVecLen t)
      (λ v → ℕPath (⟦ filterEvenOddExpr s t ⟧ (map fst v) mod two) 1)
                    (Fin2Lists (evenOddVecLen t))}
   → isOddT (⟦ s ⟧ (map fst t))
solveIsOdd s t {u = u} =
  isOddT↔≡1 (⟦ s ⟧ (map fst t)) .snd
    (solveWithConstraints s 1 t {u})

-- example: the expression r + (3 · p + 2 · q) is odd whenever p and r are
module _ (p q r : ℕ) (odp : isOddT p) (odr : isOddT r) where
  exp : Expr 3
  exp = ∣ two +' ((K 3 ·' ∣ zero) +' (K 2 ·' ∣ one))

  exp≡ : isEvenT (r + (3 · p + 2 · q))
  exp≡ = solveIsEven exp
      ((p , nope odp)
    ∷ (q , ？)
    ∷ (r , nope odr) ∷ [])
