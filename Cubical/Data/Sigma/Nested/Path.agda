{-

  From (I → Sig ℓ n) we can generate Sig ℓ (n * 3)
  in the two ways by arranging fileds in diferent order
   (this is illustrated in Example.agda)

  Of course for both definitions, the path betwen most nested arguments must be at the end,
  becouse its type depends on all the previous fields.


  In second part of this file, those generated signatures are used to
  define paths of arbitrary dimension (generalization of Path, Square and Cube from Prelude).

  The diferent order of fields results in two diferent (equivalent after uncurring)
  definitions of Pathⁿ.

  Non-primed definition have order of arguments consistent with definitions from Prelude.


-}


{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.Path where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying





sig-PathP : ∀ {ℓ} → ∀ {n}
                 → (p : I → Sig ℓ n)
                 → (x₀ : NestedΣᵣ (p i0)) → (x₁ : NestedΣᵣ (p i1))
                 → Σ[ sₚ ∈ Sig ℓ n ] (NestedΣᵣ sₚ) ≃ (PathP (λ i → NestedΣᵣ (p i)) x₀ x₁)
sig-PathP {n = 0} p x₀ x₁ = _ , isoToEquiv (iso (const refl) (const _) (λ b i j → _) λ a → refl)
sig-PathP {n = 1} p x₀ x₁ = _ , idEquiv _
sig-PathP {n = suc (suc n)} p x₀ x₁ =
  _ , compEquiv
         (Σ-cong-equiv-snd
             λ a → snd (sig-PathP (λ i → snd (p i) (a i)) _ _))
         (isoToEquiv ΣPathPIsoPathPΣ)


-- this verision is putting all the PathPs in the last fields (most nested Sigmas)

sig-PathP-withEnds : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n + n + n)
sig-PathP-withEnds {n = n} s =
   sig-cs.concat
     (sig-cs.concat _ (const (s i1)))
     (fst ∘ uncurry (sig-PathP s) ∘ nestedΣᵣ-cs.split' (s i0) _)


-- this verision is putting puting PathPs as early as it is possible
--   (just after second end is defined)

sig-PathP-withEnds' : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n * 3)
sig-PathP-withEnds' {n = 0} x = _
sig-PathP-withEnds' {n = 1} x = _ , ((_ ,_) ∘ (PathP x))
sig-PathP-withEnds' {n = suc (suc n)} x =
              _ ,
      λ x0 →  _ ,
      λ x1 → PathP _ x0 x1 ,
      λ p → sig-PathP-withEnds' λ i → snd (x i) (p i)



nestedΣᵣ-combine-to : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                 → NestedΣᵣ (sig-PathP-withEnds' p)
                 → ∀ i → NestedΣᵣ (p i)
nestedΣᵣ-combine-to {n = 0} _ _ _ = _
nestedΣᵣ-combine-to {n = 1} _ x _ = snd (snd x) _
nestedΣᵣ-combine-to {n = suc (suc n)} p x _ =
  _ , (nestedΣᵣ-combine-to ((λ _ → snd (p _) _)) (snd (snd (snd x)) ) _)

nestedΣᵣ-combine-from : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                  → (∀ i → NestedΣᵣ (p i))
                  → NestedΣᵣ (sig-PathP-withEnds' p)

nestedΣᵣ-combine-from {ℓ} {0} p x = _
nestedΣᵣ-combine-from {ℓ} {1} p x = _ , (_ , λ _ → x _)
nestedΣᵣ-combine-from {ℓ} {suc (suc n)} p x =
   _ , _ , _ , nestedΣᵣ-combine-from (λ _ → snd (p _) _) λ _ → snd (x _)


nestedΣᵣ-combine-iso : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                  → Iso (NestedΣᵣ (sig-PathP-withEnds' p))
                        (Σ[ x₀ ∈ _ ] Σ[ x₁ ∈ _ ] PathP (λ i → NestedΣᵣ (p i)) x₀ x₁)

Iso.fun (nestedΣᵣ-combine-iso p) = (λ x → _ , _ , λ _ → nestedΣᵣ-combine-to p x _)
Iso.inv (nestedΣᵣ-combine-iso p) = (λ x → nestedΣᵣ-combine-from p λ _ → (snd (snd x)) _)
Iso.rightInv (nestedΣᵣ-combine-iso {n = 0} p) b = refl
Iso.rightInv (nestedΣᵣ-combine-iso {n = 1} p) b = refl
Iso.rightInv (nestedΣᵣ-combine-iso {n = suc (suc n)} p) (_ , b) i =
  let z = Iso.rightInv (nestedΣᵣ-combine-iso λ _ → snd (p _) _)
                 (_ ,  _ , λ _ → snd (snd b _)) i
  in _ , (_ , (λ i₁ → _ , snd (snd z) i₁))

Iso.leftInv (nestedΣᵣ-combine-iso {n = 0} p) a = refl
Iso.leftInv (nestedΣᵣ-combine-iso {n = 1} p) a = refl
Iso.leftInv (nestedΣᵣ-combine-iso {n = suc (suc n)} p) a i =
 _ , _ , _ , Iso.leftInv (nestedΣᵣ-combine-iso {n = suc n} _) (snd (snd (snd a))) i



withEnds'-Iso-withEnds : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
        → Iso (NestedΣᵣ (sig-PathP-withEnds' p))
              (NestedΣᵣ (sig-PathP-withEnds p))

withEnds'-Iso-withEnds {n = n} p =  _ Iso⟨ nestedΣᵣ-combine-iso p ⟩
                   _ Iso⟨ (Σ-cong-iso-snd
                           λ x₀ → Σ-cong-iso-snd
                           λ x₁ → equivToIso (invEquiv (snd (sig-PathP p _ _)))) ⟩
                   _ Iso⟨ invIso Σ-assoc-Iso ⟩
                   _ Iso⟨ invIso (Σ-cong-iso-fst
                             (invIso (nestedΣᵣ-cs.isom-concat {n = n} {m = n} _ _))) ⟩
                   _ Iso⟨ nestedΣᵣ-cs.isom-concat {n = n + n} {m = n} _ _ ⟩ _ ∎Iso



mkSigPath : ∀ {ℓ} → ∀ n → NestedΣᵣ (sig-PathP-withEnds' (λ _ → Sig-of-Sig n)) → (I → Sig ℓ n)
mkSigPath {ℓ} n x i =
 equivFun NestedΣᵣ-≃-Sig (snd (snd (Iso.fun (nestedΣᵣ-combine-iso  {n = n} (λ _ → Sig-of-Sig n)) x)) i)









3^ : ℕ → ℕ
3^ zero = suc zero
3^ (suc x) = (3^ x) * 3

3^-lem : ∀ n → 3^ n + 3^ n + 3^ n ≡ 3^ (suc n)
3^-lem n = (λ i → +-assoc (3^ n) (3^ n) (+-zero (3^ n) (~ i)) (~ i)) ∙ *-comm 3 (3^ n)


-- this function generates explcity description for definition of Pathⁿ

-- note that for each dimension we introduce 2 explicit arguments
-- so for dimension n we will get
--    2 * n   - explicit arguments
--    (3^ n - 1 - (2 * n))  - implicit arguments

pathⁿ-args-desc : ∀ n → Vec Bool (predℕ (3^ n))
pathⁿ-args-desc 0 = []
pathⁿ-args-desc (suc n) =
 let z =   (repeat {n = predℕ (3^ n)} true)
           ++ (false ∷ (repeat {n = predℕ (3^ n)} true))
           ++ (false ∷ pathⁿ-args-desc n)
 in castImpex z

NCubeSig : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Sig ℓ (3^ n)
NCubeSig zero A = A
NCubeSig (suc n) A = sig-subst-n (3^-lem n) (sig-PathP-withEnds (λ _ → NCubeSig n A))

-- by dropping last field (the path of the highest dimension)
-- we can create signature of boundary

Boundaryⁿ : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ n A = NestedΣᵣ (dropLast (NCubeSig n A))

InsideOfⁿ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → Boundaryⁿ n A → Type ℓ
InsideOfⁿ {n = n} {A} = lastTy (NCubeSig n A)

Pathⁿ : ∀ {ℓ} → (n : ℕ) → (A : Type ℓ) → _
Pathⁿ n A = toTypeFam (pathⁿ-args-desc n) (NCubeSig n A)

NCubeSig' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Sig ℓ (3^ n)
NCubeSig' zero A = A
NCubeSig' (suc n) A = sig-PathP-withEnds' λ _ → NCubeSig' n A

Boundaryⁿ' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ' n A = NestedΣᵣ (dropLast (NCubeSig' n A))

InsideOfⁿ' : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → Boundaryⁿ' n A → Type ℓ
InsideOfⁿ' {n = n} {A} = lastTy (NCubeSig' n A)

Pathⁿ' : ∀ {ℓ} → (n : ℕ) → (A : Type ℓ) → _
Pathⁿ' n A = toTypeFam (pathⁿ-args-desc n) (NCubeSig' n A)

-- NCubeSig properly describes type of Path , Cube and Square from Prelude
-- this is _not_ the case for NCubeSig' because of diferent order of arguments

private
  Path' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 1) (NCubeSig 1 A)
  Path' = Path

Square' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 2) (NCubeSig 2 A)
Square' A = Square {A = A}

Cube' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 3) (NCubeSig 3 A)
Cube' A = Cube {A = A}

-- Pathⁿ is definationaly equall to Path, Square and Cube with type argument made explicit

Pathⁿ-1-≡-PathP : ∀ {ℓ} → Pathⁿ {ℓ} 1 ≡ Path
Pathⁿ-1-≡-PathP = refl

Pathⁿ-2-≡-Square' : ∀ {ℓ} → Pathⁿ {ℓ} 2 ≡ Square'
Pathⁿ-2-≡-Square' = refl

Pathⁿ-3-≡-Cube' : ∀ {ℓ} → Pathⁿ {ℓ} 3 ≡ Cube'
Pathⁿ-3-≡-Cube' = refl



---

record CubeR {ℓ} {bTy : Type ℓ} (cTy : bTy → Type ℓ) : Type ℓ where
  constructor cubeR

  field
    side0 side1 : bTy



Cubeⁿ : ∀ {ℓ} → ℕ → (A : Type ℓ) → Type ℓ
Cubeⁿ n A = NestedΣᵣ (NCubeSig' n A)

cubeBd : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Cubeⁿ n A → Boundaryⁿ' n A
cubeBd n A = dropLastΣᵣ ( (NCubeSig' n A))

cubeIns : ∀ {ℓ} → ∀ n → (A : Type ℓ) → (c : Cubeⁿ n A) → InsideOfⁿ' {n = n} {A} (cubeBd n A c)
cubeIns n A c = getLast ((NCubeSig' n A)) c
