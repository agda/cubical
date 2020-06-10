{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.NCube where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec )

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

NCube : ℕ → Type₀
NCube = λ n → Vec Interval n

corner0 : ∀ {n} →  NCube n
corner0 {zero} = []
corner0 {suc n} =  zero ∷ corner0

corner1 : ∀ {n} →  NCube n
corner1 {zero} = []
corner1 {suc n} =  one ∷ corner1

isPropCube : ∀ {n} → isProp (NCube n)
isPropCube {zero} [] [] i = []
isPropCube {suc n} (x ∷ x₁) (x₂ ∷ x₃) i = (isProp-Interval' x x₂ i) ∷ isPropCube x₁ x₃ i






-- Typeⁿ' : ℕ → Level → Typeω
-- Typeⁿ' zero ℓ = I → Type ℓ
-- Typeⁿ' (suc n) ℓ = I → Typeⁿ' n ℓ

-- NCube : ℕ → Type₀
-- NCube = Vec Interval

-- Typeⁿ : ℕ → ∀ ℓ → Type (ℓ-suc ℓ)
-- Typeⁿ n ℓ = NCube n → Type ℓ


-- _∘∷_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
--        → ∀ {n}
--        → (Vec A (suc n) → B) → A → (Vec A n → B)
-- A ∘∷ a = A ∘ (a ∷_ )

-- ∷∘ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
--        → ∀ {n}
--        → (A → (Vec A n → B)) → (Vec A (suc n) → B) 
-- ∷∘ x x₁ = x (head x₁) (tail x₁)

-- _∘∷-dep_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
--            → {B : Vec A (suc n) → Type ℓ'}
--            → Π B → Π (Π ∘ (B ∘∷_))
-- A ∘∷-dep a = A ∘ (a ∷_ )


-- ∷∘-dep : ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
--            → {B : Vec A (suc n) → Type ℓ'}
--            → Π (Π ∘ B ∘∷_) → Π B 
-- ∷∘-dep x (h ∷ t) = x h t

-- ∘∷-Iso :  ∀ {ℓ ℓ'} → {A : Type ℓ} → ∀ {n}
--            → {B : Vec A (suc n) → Type ℓ'}
--            → Iso (Π B) (Π (Π ∘ (B ∘∷_)))
-- Iso.fun ∘∷-Iso = _∘∷-dep_
-- Iso.inv ∘∷-Iso = ∷∘-dep
-- Iso.rightInv ∘∷-Iso b = refl
-- Iso.leftInv ∘∷-Iso a i (x ∷ x₁) = a (x ∷ x₁)


-- _∷ₗ_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A n → A → Vec A (suc n)
-- _∷ₗ_ {n = zero} x x₁ = x₁ ∷ []
-- _∷ₗ_ {n = suc n} x x₁ = head x ∷ ((tail x) ∷ₗ x₁)

-- _∘∷ₗ_ : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
--        → ∀ {n}
--        → (Vec A (suc n) → B) → A → (Vec A n → B)
-- A ∘∷ₗ a = A ∘ (_∷ₗ a )



-- Typeⁿ'→Typeⁿ : ∀ {ℓ} → ∀ n →  Typeⁿ' n ℓ → Typeⁿ (suc n) ℓ
-- Typeⁿ'→Typeⁿ zero x x₁ = I-rec (λ i → x i) (head x₁)
-- Typeⁿ'→Typeⁿ (suc n) x x₁ = I-rec (λ i →  Typeⁿ'→Typeⁿ n (x i) (tail x₁)) (head x₁)

-- Typeⁿ→Typeⁿ' : ∀ {ℓ} → ∀ n → Typeⁿ (suc n) ℓ → Typeⁿ' n ℓ
-- Typeⁿ→Typeⁿ' zero x i = x (seg i ∷ [])
-- Typeⁿ→Typeⁿ' (suc n) x i = Typeⁿ→Typeⁿ' n (x ∘∷ (seg i))



-- 3^ : ℕ → ℕ
-- 3^ zero = suc zero
-- 3^ (suc x) = (3^ x) * 3

-- -- this signature is describing record of all the cells of the n-cube

-- NCubeSig : ∀ {ℓ} → ∀ {n} → Typeⁿ n ℓ → Sigₗ ℓ (3^ n)
-- NCubeSig {n = zero} x = x []
-- NCubeSig {n = suc n} x = sigₗ-Ends-with-PathP' (λ i → NCubeSig (x ∘∷ (seg i)))

-- -- this isomorphism is betwen
-- -- dependent function from n dimensional cube
-- -- and record of 3^ n cells 

-- cubeSig-Iso : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ)
--            → Iso (Π A) (Recₗ (NCubeSig A))
-- Iso.fun (cubeSig-Iso {n = zero} _) x = x []
-- Iso.inv (cubeSig-Iso {n = zero} _) x [] = x 
-- Iso.rightInv (cubeSig-Iso {n = zero} _) _ = refl
-- Iso.leftInv (cubeSig-Iso {n = zero} A) a i [] = a []
-- cubeSig-Iso {n = suc n} A =
--   compIso
--   (compIso ∘∷-Iso (pathToIso (cong Π (funExt (isoToPath ∘ cubeSig-Iso ∘ A ∘∷_)))))
--   (sigₗ-Ends-with-PathP'-Iso-Interval (NCubeSig ∘ A ∘∷_ ))

-- PathPⁿ-explicit : ∀ {ℓ} → ∀ {n}
--                  → (A : Typeⁿ n ℓ)
--                   → Type-in-sig false [] (trim-sig (NCubeSig A) )
-- PathPⁿ-explicit x = pop-Type _ _ (NCubeSig x)

-- argsToPick : ℕ → List ℕ
-- argsToPick zero = []
-- argsToPick (suc x) = predℕ (3^ x) ∷ predℕ (3^ x) ∷ argsToPick x 

-- PathPⁿ : ∀ {ℓ} → ∀ {n}
--                  → (A : Typeⁿ n ℓ)
--                   → Type-in-sig true (argsToPick n) (trim-sig (NCubeSig A) )
-- PathPⁿ x = pop-Type _ _ (NCubeSig x)

-- Pathⁿ : ∀ {ℓ} → ∀ n
--                  → {A : Type ℓ}
--                   → Type-in-sig true (argsToPick n) (trim-sig (NCubeSig {n = n} (const A)) )
-- Pathⁿ n {x} = PathPⁿ (const x)

-- -- generated cube is definationaly equall to one from Prelude
-- Cube-test : ∀ {ℓ} → ∀ (A : Type ℓ) → 
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--   → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
--     ≡
--     Pathⁿ 3 _ _ _ _ _ _
-- Cube-test _ _ _ _ _ _ _ = refl


-- -- by discarding last field (the interior cell) we can create signature of boundary record

-- BoundaryPⁿ : ∀ {ℓ} → ∀ {n}
--                  → (A : Typeⁿ n ℓ)
--                  → Type ℓ
-- BoundaryPⁿ A = Recₗ (trim-sig (NCubeSig A) )

-- Boundaryⁿ : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
-- Boundaryⁿ n A = BoundaryPⁿ {n = n} (const A)

-- InteriorP :  ∀ {ℓ} → ∀ {n}
--                  → (A : Typeⁿ n ℓ)
--                  → BoundaryPⁿ A → Type ℓ
-- InteriorP A = pop-Type-overRecₗ (NCubeSig A)


-- Σ-Bd-Ins : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ) → Type ℓ
-- Σ-Bd-Ins A = Σ (BoundaryPⁿ A) (InteriorP A)


-- -- this isomorphism splits cube into boundary and interior

-- IsoCub : ∀ {ℓ} → ∀ {n} → (A : Typeⁿ n ℓ)
--            → Iso (Π A) (Σ (BoundaryPⁿ A) (InteriorP A))
-- IsoCub A = compIso (cubeSig-Iso A) (invIso (push-popVal-Iso (NCubeSig A)))


-- from-ends-Path :  ∀ {ℓ} → ∀ {n} → (A : Typeⁿ (suc n) ℓ)
--                   → Iso (Π (Σ-Bd-Ins ∘ A ∘∷_))
--                         (Σ-Bd-Ins A)
-- from-ends-Path  A = compIso (pathToIso p1) (compIso p2 p3)

--   where
--     p1 : ((i' : Interval) → Σ-Bd-Ins (A ∘∷ i'))
--            ≡ ((i' : Interval) → Recₗ (NCubeSig (A ∘∷ i')))
--     p1 i = (i' : Interval) → isoToPath (push-popVal-Iso (NCubeSig (A ∘∷ i'))) i

--     p2 : Iso ((i' : Interval) → Recₗ (NCubeSig (A ∘∷ i'))) (Recₗ (NCubeSig A))
--     p2 = sigₗ-Ends-with-PathP'-Iso-Interval λ x → (NCubeSig (A ∘∷ x))

--     p3 : Iso (Recₗ (NCubeSig A)) (Σ-Bd-Ins A)
--     p3 = invIso (push-popVal-Iso (NCubeSig A))




-- PathPⁿ-test-3' : ∀ {ℓ} → ∀ (A : Type ℓ) → {!!}
              
-- PathPⁿ-test-3'  A = {! PathPⁿ {n = 5}!}
