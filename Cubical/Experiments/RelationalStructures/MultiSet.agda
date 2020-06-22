-- We apply the theory of zigzag complete relations to finite multisets and association lists.
-- This is a version of Cubical.Relation.ZigZag.Applications.MultiSet that uses structured
-- relations rather than structured isomorphisms.
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.RelationalStructures.MultiSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Relation.ZigZag.Base

open import Cubical.Experiments.RelationalStructures.Base

private
 variable
  ℓ : Level
  A : Type ℓ


-- we define simple association lists without any higher constructors
data AList {ℓ} (A : Type ℓ) : Type ℓ where
 ⟨⟩ : AList A
 ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_

-- We have a count-structure on List and AList and use these to get a bisimulation between the two
module Lists&ALists {A : Type ℓ} (discA : Discrete A) where

 S = parameterized-setStructure A {ℓ = ℓ} (λ _ → unaryFun-setStructure (constant-setStructure (ℕ , isSetℕ)))

 ρ = parameterized-rel A {ℓ = ℓ} (λ _ → unaryFun-rel (constant-rel (ℕ , isSetℕ)))

 θ : isSNRS S ρ
 θ = isSNRSParameterized {ℓ₀ = ℓ} A
   (λ _ → unaryFun-setStructure (constant-setStructure (ℕ , isSetℕ)))
   (λ _ → unaryFun-rel (constant-rel (ℕ , isSetℕ)))
   (λ _ → isSNRSUnaryFun
     (constant-setStructure (ℕ , isSetℕ))
     (constant-rel (ℕ , isSetℕ))
     (isSNRSConstant (ℕ , isSetℕ)))

 -- the count-structures
 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n

 Lcount : S .struct (List A)
 Lcount a [] = zero
 Lcount a (x ∷ xs) = aux a x (discA a x) (Lcount a xs)

 ALcount : S .struct (AList A)
 ALcount a ⟨⟩ = zero
 ALcount a (⟨ x , zero ⟩∷ xs) = ALcount a xs
 ALcount a (⟨ x , suc n ⟩∷ xs) = aux a x (discA a x) (ALcount a (⟨ x , n ⟩∷ xs))

 R : List A → AList A → Type ℓ
 R xs ys = ∀ a → Lcount a xs ≡ ALcount a ys

 -- now for the bisimulation between List and Alist
 φ : List A → AList A
 φ [] = ⟨⟩
 φ (x ∷ xs) = ⟨ x , 1 ⟩∷ φ xs

 ψ : AList A → List A
 ψ ⟨⟩ = []
 ψ (⟨ x , zero ⟩∷ xs) = ψ xs
 ψ (⟨ x , suc n ⟩∷ xs) = x ∷ ψ (⟨ x , n ⟩∷ xs)


 η : ∀ x → R x (φ x)
 η [] a = refl
 η (x ∷ xs) a with (discA a x)
 ...          | yes a≡x = cong suc (η xs a)
 ...          | no  a≢x = η xs a


 -- for the other direction we need a little helper function
 ε : ∀ y → R (ψ y) y
 ε' : (x : A) (n : ℕ) (xs : AList A) (a : A)
    → Lcount a (ψ (⟨ x , n ⟩∷ xs)) ≡ ALcount a (⟨ x , n ⟩∷ xs)

 ε ⟨⟩ a = refl
 ε (⟨ x , n ⟩∷ xs) a = ε' x n xs a

 ε' x zero xs a = ε xs a
 ε' x (suc n) xs a with discA a x
 ...                 | yes a≡x = cong suc (ε' x n xs a)
 ...                 | no  a≢x = ε' x n xs a

 -- Induced quotients and equivalence

 open isBisimulation

 -- R is a bisimulation
 isBisimR : isBisimulation R
 isBisimR .zigzag r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)
 isBisimR .fwd = φ
 isBisimR .fwdRel = η
 isBisimR .bwd = ψ
 isBisimR .bwdRel = ε
 isBisimR .prop xs y = isPropΠ λ _ → isSetℕ _ _

 module E = Bisim→Equiv (R , isBisimR)
 open E renaming (Rᴸ to Rᴸ; Rᴿ to Rᴬᴸ)

 List/Rᴸ = (List A) / Rᴸ
 AList/Rᴬᴸ = (AList A) / Rᴬᴸ

 List/Rᴸ≃AList/Rᴬᴸ : List/Rᴸ ≃ AList/Rᴬᴸ
 List/Rᴸ≃AList/Rᴬᴸ = E.Thm

 main : BisimDescends _ _ (List A , Lcount) (AList A , ALcount) (R , isBisimR)
 main = θ .isSNRS.descends (R , isBisimR) .fst (λ a r → r a)

 open BisimDescends

 List/Rᴸ-structure : S .struct List/Rᴸ
 List/Rᴸ-structure = main .quoᴸ .fst

 AList/Rᴬᴸ-structure : S .struct AList/Rᴬᴸ
 AList/Rᴬᴸ-structure = main .quoᴿ .fst

 -- We get that the equivalence is an isomorphism directly from the fact that is induced by a bisimulation

 List/Rᴸ≡AList/Rᴬᴸ :
   Path (TypeWithStr ℓ (S .struct)) (List/Rᴸ , List/Rᴸ-structure) (AList/Rᴬᴸ , AList/Rᴬᴸ-structure)
 List/Rᴸ≡AList/Rᴬᴸ =  ΣPathP (ua E.Thm , main .path)
