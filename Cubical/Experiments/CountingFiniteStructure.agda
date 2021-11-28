{-

Counting how many structured finite sets with a given cardinal

https://github.com/EgbertRijke/OEIS-A000001

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.CountingFiniteStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Decidability
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.FinType
open import Cubical.Data.FinSet.FiniteStructure

private
  variable
    ℓ : Level

-- convenient abbreviation

isFinStrCard : (S : FinSet ℓ-zero → FinSet ℓ) (n : ℕ) → isFinType 0 (FinSetWithStrOfCard ℓ-zero S n)
isFinStrCard S n = isFinTypeFinSetWithStrOfCard ℓ-zero S n

-- structure that there is no structure

TrivialStr : FinSet ℓ → FinSet ℓ
TrivialStr _ = 𝟙

-- structure that "picking an element in that set"

IdentityStr : FinSet ℓ → FinSet ℓ
IdentityStr X = X

-- finite semi-groups

FinSemiGroupStr : FinSet ℓ → FinSet ℓ
FinSemiGroupStr X .fst =
  Σ[ p ∈ (X .fst → X .fst → X .fst) ] ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
FinSemiGroupStr X .snd =
  isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X))
    (λ p → _ , isFinSetΠ3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isFinSet≡ X _ _))

-- finite groups

FinGroupStr : FinSet ℓ → FinSet ℓ
FinGroupStr X .fst =
  Σ[ e ∈ X .fst ]
    Σ[ inv ∈ (X .fst → X .fst) ]
      Σ[ p ∈ (X .fst → X .fst → X .fst) ]
          ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
        × ((x : X .fst)
            → (p x e ≡ x) × (p e x ≡ x) × (p (inv x) x ≡ e) × (p x (inv x) ≡ e))
FinGroupStr X .snd =
  isFinSetΣ X (λ _ → _ ,
    isFinSetΣ (_ , isFinSetΠ X (λ _ → X)) (λ _ → _ ,
      isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → _ ,
        isFinSet× (_ , isFinSetΠ3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isFinSet≡ X _ _)) (_ ,
          isFinSetΠ X (λ _ → _ ,
            isFinSet× (_ , isFinSet≡ X _ _) (_ ,
              isFinSet× (_ , isFinSet≡ X _ _) (_ ,
                isFinSet× (_ , isFinSet≡ X _ _) (_ , isFinSet≡ X _ _))))))))

-- two rather trivial numbers
-- but the computation is essentially not that trivial
-- this one can be computed in half-a-minute
a2 : ℕ
a2 = card (_ , isFinStrCard TrivialStr 2)

-- this is already hard to compute
-- it takes less than half-an-hour
b2 : ℕ
b2 = card (_ , isFinStrCard IdentityStr 2)

-- the number of finite semi-groups
numberOfFinSemiGroups : ℕ → ℕ
numberOfFinSemiGroups n = card (_ , isFinStrCard FinSemiGroupStr n)

-- two trivial cases of semi-groups
-- in a flash
n0 : ℕ
n0 = numberOfFinSemiGroups 0

-- nearly one minute
n1 : ℕ
n1 = numberOfFinSemiGroups 1

-- the number of finite semi-groups with cardinal 2
-- it should be 5
-- would you like to try?
n2 : ℕ
n2 = numberOfFinSemiGroups 2

-- OEIS-A000001
-- I think you'd better not evaluate this function with n > 1
numberOfFinGroups : ℕ → ℕ
numberOfFinGroups n = card (_ , isFinStrCard FinGroupStr n)

-- group with one element
-- it takes about 21 minutes
g1 : ℕ
g1 = numberOfFinGroups 1

-- Rijke's challenge
-- seemed to big to do an exhaustive search
g4 : ℕ
g4 = numberOfFinGroups 4

--------------- test -----------------

open import Cubical.Data.SumFin

k : ℕ
k = card (FinSemiGroupStr (Fin 3 , isFinSetFin))

EndoStr : FinSet ℓ → FinSet ℓ
EndoStr X = (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X))

EndoStr' : FinSet ℓ → FinSet ℓ
EndoStr' {ℓ = ℓ} X = (_ , isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → 𝟙 {ℓ}))

EndoStr'' : FinSet ℓ → FinSet ℓ
EndoStr'' {ℓ = ℓ} X = (_ , isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → (Fin 1 , isFinSetFin)))

open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

{-
isDecPropUnit : isDecProp Unit
isDecPropUnit .fst = isPropUnit
isDecPropUnit .snd = yes tt
-}
isDecPropUnit : isDecProp Unit
isDecPropUnit .fst = true
isDecPropUnit .snd = idEquiv _

EndoStr''' : FinSet ℓ → FinSet ℓ
EndoStr''' {ℓ = ℓ} X = (_ , isFinSetSub (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → Unit , isDecPropUnit))

l : ℕ
l = card (EndoStr (Fin 3 , isFinSetFin))

l' : ℕ
l' = card (EndoStr' (Fin 3 , isFinSetFin))

l'' : ℕ
l'' = card (EndoStr'' (Fin 2 , isFinSetFin))

l''' : ℕ
l''' = card (EndoStr''' (Fin 3 , isFinSetFin))

FinSemiGroupStr' : FinSet ℓ → FinSet ℓ
FinSemiGroupStr' X .fst =
  Σ[ p ∈ (X .fst → X .fst → X .fst) ] ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
FinSemiGroupStr' X .snd =
  isFinSetSub (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X))
    (λ p → _ , isDecProp∀3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isDecProp≡ X _ _))

k' : ℕ
k' = card (FinSemiGroupStr' (Fin 2 , isFinSetFin))

k'' : ℕ
k'' = card (FinSemiGroupStr (Fin 2 , isFinSetFin))

FinGroupStr' : FinSet ℓ → FinSet ℓ
FinGroupStr' X .fst =
  Σ[ e ∈ X .fst ]
    Σ[ inv ∈ (X .fst → X .fst) ]
      Σ[ p ∈ (X .fst → X .fst → X .fst) ]
          ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
        × ((x : X .fst)
            → (p x e ≡ x) × (p e x ≡ x) × (p (inv x) x ≡ e) × (p x (inv x) ≡ e))
FinGroupStr' X .snd =
  isFinSetΣ X (λ _ → _ ,
    isFinSetΣ (_ , isFinSetΠ X (λ _ → X)) (λ _ → _ ,
      isFinSetSub (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → _ ,
        isDecProp× (_ , isDecProp∀3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isDecProp≡ X _ _)) (_ ,
          isDecProp∀ X (λ _ → _ ,
            isDecProp× (_ , isDecProp≡ X _ _) (_ ,
              isDecProp× (_ , isDecProp≡ X _ _) (_ ,
                isDecProp× (_ , isDecProp≡ X _ _) (_ , isDecProp≡ X _ _))))))))

r : ℕ
r = card (FinGroupStr' (Fin 2 , isFinSetFin))

r' : ℕ
r' = card (FinGroupStr (Fin 2 , isFinSetFin))

ff : ℕ → ℕ
ff n = card (_ , isFinStrCard FinSemiGroupStr n)

ff' : ℕ → ℕ
ff' n = card (_ , isFinStrCard FinSemiGroupStr' n)
