-- We apply the theory of quasi equivalence relations (QERs) to finite multisets and association lists.
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.ZigZag.Applications.MultiSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
open import Cubical.HITs.FiniteMultiset.CountExtensionality
open import Cubical.Relation.Nullary
open import Cubical.Relation.ZigZag.Base

open import Cubical.Structures.MultiSet
open import Cubical.Structures.Relational.Macro

-- we define simple association lists without any higher constructors
data AList {ℓ} (A : Type ℓ) : Type ℓ where
 ⟨⟩ : AList A
 ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_

private
 variable
  ℓ : Level
  A : Type ℓ

-- We have a CountStructure on List and AList and use these to get a QER between the two
module Lists&ALists {A : Type ℓ} (discA : Discrete A) where

 module S = RelMacro ℓ (param A (recvar (constant (ℕ , isSetℕ))))

 ι = CountEquivStr A (Discrete→isSet discA)

 -- the CountStructures
 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n

 Lcount : S.structure (List A)
 Lcount a [] = zero
 Lcount a (x ∷ xs) = aux a x (discA a x) (Lcount a xs)

 ALcount : S.structure (AList A)
 ALcount a ⟨⟩ = zero
 ALcount a (⟨ x , zero ⟩∷ xs) = ALcount a xs
 ALcount a (⟨ x , suc n ⟩∷ xs) = aux a x (discA a x) (ALcount a (⟨ x , n ⟩∷ xs))

 -- now for the QER between List and Alist

 R : List A → AList A → Type ℓ
 R xs ys = ∀ a → Lcount a xs ≡ ALcount a ys

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

 open isQuasiEquivRel

 -- R is a QER
 QuasiR : QuasiEquivRel _ _ ℓ
 QuasiR .fst .fst = R
 QuasiR .fst .snd _ _ = isPropΠ λ _ → isSetℕ _ _
 QuasiR .snd .zigzag r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)
 QuasiR .snd .fwd = φ
 QuasiR .snd .fwdRel = η
 QuasiR .snd .bwd = ψ
 QuasiR .snd .bwdRel = ε

 module E = QER→Equiv QuasiR
 open E renaming (Rᴸ to Rᴸ; Rᴿ to Rᴬᴸ)

 List/Rᴸ = (List A) / Rᴸ
 AList/Rᴬᴸ = (AList A) / Rᴬᴸ

 List/Rᴸ≃AList/Rᴬᴸ : List/Rᴸ ≃ AList/Rᴬᴸ
 List/Rᴸ≃AList/Rᴬᴸ = E.Thm

 main : QERDescends _ S.relation (List A , Lcount) (AList A , ALcount) QuasiR
 main = structuredQER→structuredEquiv _ S.suitable _ _ QuasiR (λ a r → r a)

 open QERDescends

 LQcount : S.structure List/Rᴸ
 LQcount = main .quoᴸ .fst

 ALQcount : S.structure AList/Rᴬᴸ
 ALQcount = main .quoᴿ .fst

 -- We get a path between CountStructures over the equivalence directly from the fact that the QER
 -- is structured
 List/Rᴸ≡AList/Rᴬᴸ :
   Path (TypeWithStr ℓ S.structure) (List/Rᴸ , LQcount) (AList/Rᴬᴸ , ALQcount)
 List/Rᴸ≡AList/Rᴬᴸ =
   sip S.univalent _ _ (E.Thm , (S.matches _ _ E.Thm .fst (main .rel)))

 -- We now show that List/Rᴸ≃FMSet
 _∷/_ : A → List/Rᴸ → List/Rᴸ
 a ∷/ [ xs ] = [ a ∷ xs ]
 a ∷/ eq/ xs xs' r i = eq/ (a ∷ xs) (a ∷ xs') r' i
  where
  r' : Rᴸ (a ∷ xs) (a ∷ xs')
  r' a' = cong (aux a' a (discA a' a)) (r a')
 a ∷/ squash/ xs xs₁ p q i j = squash/ (a ∷/ xs) (a ∷/ xs₁) (cong (a ∷/_) p) (cong (a ∷/_) q) i j

 infixr 5 _∷/_

 μ : FMSet A → List/Rᴸ
 μ = FMS.Rec.f squash/ [ [] ] _∷/_ β
  where
  β : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
  β a b = elimProp (λ _ → squash/ _ _) (λ xs → eq/ _ _ (γ xs))
   where
     γ : ∀ xs → Rᴸ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
     γ xs c = δ c ∙ η (b ∷ a ∷ xs) c
      where
      δ : ∀ c → Lcount c (a ∷ b ∷ xs) ≡ Lcount c (b ∷ a ∷ xs)
      δ c with discA c a | discA c b
      δ c | yes _        | yes _ = refl
      δ c | yes _        | no  _ = refl
      δ c | no  _        | yes _ = refl
      δ c | no  _        | no  _ = refl


 -- The inverse is induced by the standard projection of lists into finite multisets,
 -- which is a morphism of CountStructures
 -- Moreover, we need 'count-extensionality' for finite multisets
 List→FMSet : List A → FMSet A
 List→FMSet [] = []
 List→FMSet (x ∷ xs) = x ∷ List→FMSet xs

 List→FMSet-count : ∀ a xs → Lcount a xs ≡ FMScount discA a (List→FMSet xs)
 List→FMSet-count a [] = refl
 List→FMSet-count a (x ∷ xs) with discA a x
 ...                         | yes _ = cong suc (List→FMSet-count a xs)
 ...                         | no  _ = List→FMSet-count a xs


 ν : List/Rᴸ → FMSet A
 ν [ xs ] = List→FMSet xs
 ν (eq/ xs ys r i) = path i
  where
   countsAgree : ∀ a → Lcount a xs ≡ Lcount a ys
   countsAgree a = r a ∙ sym (η ys a)

   θ : ∀ a → FMScount discA a (List→FMSet xs) ≡ FMScount discA a (List→FMSet ys)
   θ a = sym (List→FMSet-count a xs) ∙∙ countsAgree a ∙∙ List→FMSet-count a ys

   path : List→FMSet xs ≡ List→FMSet ys
   path = FMScountExt.Thm discA _ _ θ
 ν (squash/ xs/ xs/' p q i j) = trunc (ν xs/) (ν xs/') (cong ν p) (cong ν q) i j


 σ : section μ ν
 σ = elimProp (λ _ → squash/ _ _) θ
  where
  θ : (xs : List A) → μ (ν [ xs ]) ≡ [ xs ]
  θ [] = refl
  θ (x ∷ xs) = cong (x ∷/_) (θ xs)


 ν-∷/-commute : (x : A) (ys : List/Rᴸ) → ν (x ∷/ ys) ≡ x ∷ ν ys
 ν-∷/-commute x = elimProp (λ _ → FMS.trunc _ _) λ xs → refl

 τ : retract μ ν
 τ = FMS.ElimProp.f (FMS.trunc _ _) refl θ
  where
  θ : ∀ x {xs} → ν (μ xs) ≡ xs → ν (μ (x ∷ xs)) ≡ x ∷ xs
  θ x {xs} p = ν-∷/-commute x (μ xs) ∙ cong (x ∷_) p

 List/Rᴸ≃FMSet : List/Rᴸ ≃ FMSet A
 List/Rᴸ≃FMSet = isoToEquiv (iso ν μ τ σ)

 List/Rᴸ≃FMSet-is-CountEquivStr : ι (List/Rᴸ , LQcount) (FMSet A , FMScount discA) List/Rᴸ≃FMSet
 List/Rᴸ≃FMSet-is-CountEquivStr a = elimProp (λ _ → isSetℕ _ _) (List→FMSet-count a)

 {-
 Putting everything together we get:
               ≃
 List/Rᴸ ------------> AList/Rᴬᴸ
   |
   |≃
   |
   ∨
               ≃
 FMSet A ------------> AssocList A
 We thus get that AList/Rᴬᴸ≃AssocList.
 Constructing such an equivalence directly requires count extensionality for association lists,
 which should be even harder to prove than for finite multisets.
 This strategy should work for all implementations of multisets with HITs.
 We just have to show that:
  ∙ The HIT is equivalent to FMSet (like AssocList)
  ∙ There is a QER between lists and the basic data type of the HIT
    with the higher constructors removed (like AList)
 Then we get that this HIT is equivalent to the corresponding set quotient that identifies elements
 that give the same count on each a : A.
 TODO: Show that all the equivalences are indeed isomorphisms of multisets not only of CountStructures!
 -}
