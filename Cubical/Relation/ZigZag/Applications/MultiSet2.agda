-- We apply the theory of zigzag complete relations to finite multisets and association lists.
{-# OPTIONS --cubical --no-import-sorts #-}
module Cubical.Relation.ZigZag.Applications.MultiSet2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Structures.Relational
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.ZigZag.Base as ZigZag

private
 variable
  ℓ : Level
  A : Type ℓ


-- we define simple association lists without any higher constructors
data AList (A : Type ℓ) : Type ℓ where
 ⟨⟩ : AList A
 ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_

postulate -- TODO
  isOfHLevelAList : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
    → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (AList A)

-- We have a count-structure on List and AList and use these to get a bisimulation between the two
module Lists&ALists {A : Type ℓ} (discA : Discrete A) where

  S = parameterized-structure {ℓ₁ = ℓ} A (λ _ → unaryFun-structure (constant-structure (ℕ , isSetℕ)))

 ρ = parameterized-rel {ℓ₁ = ℓ} A
   (λ _ → unaryFun-structure (constant-structure (ℕ , isSetℕ)))
   (λ _ → unaryFun-rel (constant-structure (ℕ , isSetℕ)) (constant-rel (ℕ , isSetℕ)))

 θ = isSNRSParameterized {ℓ₁ = ℓ} A
   (λ _ → unaryFun-rel (constant-structure (ℕ , isSetℕ)) (constant-rel (ℕ , isSetℕ)))
   (λ _ → isSNRSUnaryFun
     (constant-rel (ℕ , isSetℕ))
     (isSNRSConstant (ℕ , isSetℕ)))

 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n


 -- the count-structures
 Lcount : S (List A , isOfHLevelList 0 (Discrete→isSet discA)) .fst
 Lcount a [] = zero
 Lcount a (x ∷ xs) = aux a x (discA a x) (Lcount a xs)

 ALcount : S (AList A , isOfHLevelAList 0 (Discrete→isSet discA)) .fst
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

 main =
   θ ((List A , isOfHLevelList 0 (Discrete→isSet discA)) , Lcount)
     ((AList A , isOfHLevelAList 0 (Discrete→isSet discA)) , ALcount)
     (R , isBisimR)
     (λ a _ _ r → r a)

 open Descends

 List/Rᴸ-structure : S (List/Rᴸ , squash/) .fst
 List/Rᴸ-structure = main .quoᴸ .fst .fst

 AList/Rᴬᴸ-structure : S (AList/Rᴬᴸ , squash/) .fst
 AList/Rᴬᴸ-structure = main .quoᴿ .fst .fst

 -- We get that the equivalence is an isomorphism directly from the fact that is induced by a bisimulation

 List/Rᴸ≡AList/Rᴬᴸ :
   Path (Σ (hSet ℓ) (fst ∘ S))
     ((List/Rᴸ , squash/) , List/Rᴸ-structure)
     ((AList/Rᴬᴸ , squash/) , AList/Rᴬᴸ-structure)
 List/Rᴸ≡AList/Rᴬᴸ =  ΣPathP (setUA _ _ E.Thm , main .path)
