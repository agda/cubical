-- We apply the theory of zigzag complete relations to finite multisets and association lists.
-- This is a version of Cubical.Relation.ZigZag.Applications.MultiSet that uses structured
-- relations rather than structured isomorphisms.
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.RelationalStructures.MultiSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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

isSetAList : ∀ {ℓ} {A : Type ℓ} → isSet A → isSet (AList A)
isSetAList {ℓ} {A} setA xs ys =
  isOfHLevelRetract 1
    (encode xs ys)
    (decode xs ys)
    (decodeEncode xs ys)
    (isPropCover xs ys)
  where
  Cover : AList A → AList A → Type ℓ
  Cover ⟨⟩ ⟨⟩ = Lift Unit
  Cover ⟨⟩ (⟨ y , n ⟩∷ ys) = Lift ⊥
  Cover (⟨ x , n ⟩∷ xs) ⟨⟩ = Lift ⊥
  Cover (⟨ x , n ⟩∷ xs) (⟨ y , m ⟩∷ ys) = (x ≡ y) × (n ≡ m) × Cover xs ys

  encodeRefl : ∀ xs → Cover xs xs
  encodeRefl ⟨⟩ = _
  encodeRefl (⟨ x , n ⟩∷ xs) = refl , refl , encodeRefl xs

  encode : ∀ xs ys → xs ≡ ys → Cover xs ys
  encode xs _ p = subst (Cover xs) p (encodeRefl xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode ⟨⟩ ⟨⟩ _ = refl
  decode (⟨ x , n ⟩∷ xs) (⟨ y , m ⟩∷ ys) (xy , nm , c) i = ⟨ xy i , nm i ⟩∷ decode _ _ c i

  decodeEncodeRefl : ∀ xs → decode xs xs (encodeRefl xs) ≡ refl
  decodeEncodeRefl ⟨⟩ = refl
  decodeEncodeRefl (⟨ x , n ⟩∷ xs) = cong (cong ⟨ x , n ⟩∷_) (decodeEncodeRefl xs)

  decodeEncode : ∀ xs ys p → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs ys =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (transportRefl _) ∙ decodeEncodeRefl xs)

  isPropCover : ∀ xs ys → isProp (Cover xs ys)
  isPropCover ⟨⟩ ⟨⟩ = isOfHLevelLift 1 (isOfHLevelUnit 1)
  isPropCover ⟨⟩ (⟨ y , m ⟩∷ ys) = isOfHLevelLift 1 isProp⊥
  isPropCover (⟨ x , n ⟩∷ xs) ⟨⟩ = isOfHLevelLift 1 isProp⊥
  isPropCover (⟨ x , n ⟩∷ xs) (⟨ y , m ⟩∷ ys) =
    isProp× (setA x y) (isProp× (isSetℕ n m) (isPropCover xs ys))

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

 ALcount : S (AList A , isSetAList (Discrete→isSet discA)) .fst
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

 main : Descends _ _
   ((List A , isOfHLevelList 0 (Discrete→isSet discA)) , Lcount)
   ((AList A , isSetAList (Discrete→isSet discA)) , ALcount)
   (R , isBisimR)
 main = θ (R , isBisimR) (λ a r → r a)

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
