{-

Definition of and facts about Smith normal form

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Smith.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
  hiding   (_·_)
  renaming (_+_ to _+ℕ_ ; +-assoc to +Assocℕ)
open import Cubical.Data.Int
  hiding   (_+_ ; _·_ ; _-_ ; -_ ; addEq)
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.FinData

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit  as Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
  renaming (ℤ to ℤRing)

private
  variable
    m n k : ℕ

open Coefficient  ℤRing


-- Sequence of consecutively divisible integers

_∣all_ : ℤ → List ℤ → Type
n ∣all [] = ¬ n ≡ 0
n ∣all (x ∷ ys) = n ∣ x × n ∣all ys

isProp∣all : {n : ℤ}{xs : List ℤ} → isProp (n ∣all xs)
isProp∣all {xs = []}= isPropΠ (λ _ → isProp⊥)
isProp∣all {xs = x ∷ xs} = isProp× isProp∣ isProp∣all

isConsDivs : List ℤ → Type
isConsDivs [] = Unit
isConsDivs (x ∷ xs) = x ∣all xs × isConsDivs xs

isPropIsConsDivs : (xs : List ℤ) → isProp (isConsDivs xs)
isPropIsConsDivs [] = isPropUnit
isPropIsConsDivs (x ∷ xs) = isProp× isProp∣all (isPropIsConsDivs xs)

ConsDivs : Type
ConsDivs = Σ[ xs ∈ List ℤ ] isConsDivs xs

cons : (n : ℤ)(xs : ConsDivs) → n ∣all xs .fst → ConsDivs
cons n (xs , _) _ .fst = n ∷ xs
cons n ([] , _) p .snd = p , tt
cons n (x ∷ xs , q) p .snd = p , q


-- Smith normal matrix

_+length_ : ConsDivs → ℕ → ℕ
xs +length n = length (xs .fst) +ℕ n

smithMat : (xs : List ℤ)(m n : ℕ) → Mat (length xs +ℕ m) (length xs +ℕ n)
smithMat [] _ _ = 𝟘
smithMat (x ∷ xs) _ _ = x ⊕ smithMat xs _ _

smithMat∣ :
    (a : ℤ)(xs : ConsDivs){m n : ℕ}
  → ¬ a ≡ 0
  → ((i : Fin (xs +length m))(j : Fin (xs +length n)) → a ∣ smithMat (xs .fst) m n i j)
  → a ∣all xs .fst
smithMat∣ _ ([] , _) q _ = q
smithMat∣ a (x ∷ xs , p) q h = h zero zero , smithMat∣ a (xs , p .snd) q (λ i j → h (suc i) (suc j))

smithMat⊕ :
    (a : ℤ)(xs : ConsDivs){m n : ℕ}
  → (div : a ∣all xs .fst)
  → a ⊕ smithMat (xs .fst) m n ≡ smithMat (cons a xs div .fst) m n
smithMat⊕ _ _ _ = refl


-- Matrix with smith normality

record isSmithNormal (M : Mat m n) : Type where
  field
    divs : ConsDivs
    rowNull : ℕ
    colNull : ℕ

    rowEq : divs +length rowNull ≡ m
    colEq : divs +length colNull ≡ n
    matEq : PathP (λ t → Mat (rowEq t) (colEq t)) (smithMat (divs .fst) rowNull colNull) M

open isSmithNormal

row col : {M : Mat m n} → isSmithNormal M → ℕ
row isNorm = isNorm .divs +length isNorm .rowNull
col isNorm = isNorm .divs +length isNorm .colNull

smith∣ :
    (a : ℤ){M : Mat m n}(isNorm : isSmithNormal M)
  → ¬ a ≡ 0
  → ((i : Fin m)(j : Fin n) → a ∣ M i j)
  → a ∣all isNorm . divs .fst
smith∣ a isNorm p h =
  let a∣smith = λ
        { i j →
          subst (a ∣_) (λ t → isNorm .matEq (~ t)
            (subst-filler Fin (isNorm .rowEq) i (~ t))
            (subst-filler Fin (isNorm .colEq) j (~ t))) (h _ _) }
  in  smithMat∣ _ (isNorm .divs) p a∣smith


-- Similarity to a normal form

open Sim

record Smith (M : Mat m n) : Type where
  field
    sim : Sim M
    isnormal : isSmithNormal (sim .result)

open Smith

simSmith : {M : Mat m n}(sim : Sim M) → Smith (sim .result) → Smith M
simSmith simM smith = record { sim = compSim simM (smith .sim) ; isnormal = smith .isnormal }


-- Simple special cases of normal matrices

isSmithNormal𝟘 : isSmithNormal (𝟘 {m = m} {n = n})
isSmithNormal𝟘 {m = m} {n = n} =
  record
    { divs = [] , tt
    ; rowNull = m   ; colNull = n
    ; rowEq = refl  ; colEq = refl
    ; matEq = refl  }

isSmithNormalEmpty : (M : Mat 0 n) → isSmithNormal M
isSmithNormalEmpty {n = n} M =
  record
    { divs = [] , tt
    ; rowNull = 0   ; colNull = n
    ; rowEq = refl  ; colEq = refl
    ; matEq = isContr→isProp isContrEmpty _ _ }

isSmithNormalEmptyᵗ : (M : Mat m 0) → isSmithNormal M
isSmithNormalEmptyᵗ {m = m} M =
  record
    { divs = [] , tt
    ; rowNull = m   ; colNull = 0
    ; rowEq = refl  ; colEq = refl
    ; matEq = isContr→isProp isContrEmptyᵗ _ _ }

smith𝟘 : Smith (𝟘 {m = m} {n = n})
smith𝟘 = record { sim = idSim _ ; isnormal = isSmithNormal𝟘 }

smithEmpty : (M : Mat 0 n) → Smith M
smithEmpty M = record { sim = idSim _ ; isnormal = isSmithNormalEmpty M }

smithEmptyᵗ : (M : Mat m 0) → Smith M
smithEmptyᵗ M = record { sim = idSim _ ; isnormal = isSmithNormalEmptyᵗ M }
