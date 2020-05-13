-- We apply the theory of zigzag complete relations to finite multisets and association lists.
-- See discussion at the end of the file.
{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.ZigZag.Applications.MultiSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Structures.MultiSet renaming (count-structure to S)
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.FiniteMultiset as FMS hiding ([_])
open import Cubical.HITs.FiniteMultiset.Order as FMSO
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.ZigZag.Base as ZigZag

private
 variable
  ℓ : Level
  A : Type₀


-- we define simple association lists without any higher constructors
data AList (A : Type₀) : Type₀ where
 ⟨⟩ : AList A
 ⟨_,_⟩∷_ : A → ℕ → AList A → AList A

infixr 5 ⟨_,_⟩∷_


-- We have a count-structure on List and AList and use these to get a bisimulation between the two
module Lists&ALists (discA : Discrete A) where
 -- the relation we're interested in
 R : {A B : TypeWithStr ℓ-zero (S A (Discrete→isSet discA))} → (A .fst) → (B .fst) → Type₀
 R {X , count₁} {Y , count₂} x y = ∀ a → count₁ a x ≡ count₂ a y

 -- relation between R and ι
 ι = count-iso A (Discrete→isSet discA)
 ι-R-char : {X Y : TypeWithStr ℓ-zero (S A (Discrete→isSet discA))} (e : (X .fst) ≃ (Y .fst))
          → (∀ x → R {X} {Y} x (e .fst x)) ≃ (ι X Y e)
 ι-R-char e = isoToEquiv (iso (λ f → λ a x → f x a) (λ g → λ x a → g a x) (λ _ → refl) λ _ → refl)


 aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
 aux a x (yes a≡x) n = suc n
 aux a x (no  a≢x) n = n


 -- the count-structures
 Lcount : S A (Discrete→isSet discA) (List A)
 Lcount a [] = zero
 Lcount a (x ∷ xs) = aux a x (discA a x) (Lcount a xs)

 ALcount : S A (Discrete→isSet discA) (AList A)
 ALcount a ⟨⟩ = zero
 ALcount a (⟨ x , zero ⟩∷ xs) = ALcount a xs
 ALcount a (⟨ x , suc n ⟩∷ xs) = aux a x (discA a x) (ALcount a (⟨ x , n ⟩∷ xs))


 -- now for the bisimulation between List and Alist
 φ : List A → AList A
 φ [] = ⟨⟩
 φ (x ∷ xs) = ⟨ x , 1 ⟩∷ φ xs

 ψ : AList A → List A
 ψ ⟨⟩ = []
 ψ (⟨ x , zero ⟩∷ xs) = ψ xs
 ψ (⟨ x , suc n ⟩∷ xs) = x ∷ ψ (⟨ x , n ⟩∷ xs)


 η : ∀ x → R {List A , Lcount} {AList A , ALcount} x (φ x)
 η [] a = refl
 η (x ∷ xs) a  with (discA a x)
 ...           | yes a≡x = cong suc (η xs a)
 ...           | no  a≢x = η xs a


 -- for the other direction we need a little helper function
 ε : ∀ y → R {List A , Lcount} {AList A , ALcount} (ψ y) y
 ε' : (x : A) (n : ℕ) (xs : AList A) (a : A)
    → Lcount a (ψ (⟨ x , n ⟩∷ xs)) ≡ ALcount a (⟨ x , n ⟩∷ xs)

 ε ⟨⟩ a = refl
 ε (⟨ x , n ⟩∷ xs) a = ε' x n xs a

 ε' x zero xs a = ε xs a
 ε' x (suc n) xs a with discA a x
 ...                 | yes a≡x = cong suc (ε' x n xs a)
 ...                 | no  a≢x = ε' x n xs a


 -- R {List A , Lcount} {AList A , ALcount} is zigzag-complete
 zigzagR : isZigZagComplete (R {List A , Lcount} {AList A , ALcount})
 zigzagR _ _ _ _ r r' r'' a = (r a) ∙∙ sym (r' a) ∙∙ (r'' a)


 -- now we can apply the main result about zigzag-complete relations:
 Rᴸ  = ZigZag.Bisimulation→Equiv.Rᴬ (List A) (AList A) (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)
 Rᴬᴸ = ZigZag.Bisimulation→Equiv.Rᴮ (List A) (AList A) (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)

 List/Rᴸ = (List A) / Rᴸ
 AList/Rᴬᴸ = (AList A) / Rᴬᴸ

 List/Rᴸ≃AList/Rᴬᴸ : List/Rᴸ ≃ AList/Rᴬᴸ
 List/Rᴸ≃AList/Rᴬᴸ = ZigZag.Bisimulation→Equiv.Thm (List A) (AList A)
                                                   (R {List A , Lcount} {AList A , ALcount}) φ ψ (zigzagR , η , ε)

 --We want to show that this is an isomorphism of count-structures.
 --For this we first have to define the count-functions
 LQcount : A → List/Rᴸ → ℕ
 LQcount a [ xs ] = Lcount a xs
 LQcount a (eq/ xs ys r i) = ρ a i
  where
  ρ : ∀ a → Lcount a xs ≡ Lcount a ys
  ρ a = (r .snd .fst a) ∙ sym (r .snd .snd a)
 LQcount a (squash/ xs/ xs/₁ p q i j) =
         isSetℕ (LQcount a xs/) (LQcount a xs/₁) (cong (LQcount a) p) (cong (LQcount a) q) i j


 ALQcount : A → AList/Rᴬᴸ → ℕ
 ALQcount a [ xs ] = ALcount a xs
 ALQcount a (eq/ xs ys r i) = ρ a i
  where
  ρ : ∀ a → ALcount a xs ≡ ALcount a ys
  ρ a = sym (r .snd .fst a) ∙ (r .snd .snd a)
 ALQcount a (squash/ xs/ xs/₁ p q i j) =
          isSetℕ (ALQcount a xs/) (ALQcount a xs/₁) (cong (ALQcount a) p) (cong (ALQcount a) q) i j

 -- We get that the equivalence is an isomorphism directly from the fact that is induced by a bisimulation
 -- and the fact that we can characterize ι (count-iso) in terms of R
 ξ = List/Rᴸ≃AList/Rᴬᴸ .fst

 observation : (xs : List A) → R {List/Rᴸ , LQcount} {AList/Rᴬᴸ , ALQcount} [ xs ] (ξ [ xs ])
 observation = η

 ξ-is-count-iso : ι (List/Rᴸ , LQcount) (AList/Rᴬᴸ , ALQcount) List/Rᴸ≃AList/Rᴬᴸ
 ξ-is-count-iso = ι-R-char {Y = (AList/Rᴬᴸ , ALQcount)} List/Rᴸ≃AList/Rᴬᴸ .fst
                           (elimProp (λ _ → isPropΠ (λ _ → isSetℕ _ _)) observation)


 -- We now show that List/Rᴸ≃FMSet
 _∷/_ : A → List/Rᴸ → List/Rᴸ
 a ∷/ [ xs ] = [ a ∷ xs ]
 a ∷/ eq/ xs xs' r i = eq/ (a ∷ xs) (a ∷ xs') r' i
  where
  r' : Rᴸ (a ∷ xs) (a ∷ xs')
  r' =  ⟨ a , 1 ⟩∷ (r .fst)
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .fst a'))
      , (λ a' → cong (λ n →  aux a' a (discA a' a) n) (r .snd .snd a'))
 a ∷/ squash/ xs xs₁ p q i j = squash/ (a ∷/ xs) (a ∷/ xs₁) (cong (a ∷/_) p) (cong (a ∷/_) q) i j

 infixr 5 _∷/_

 μ : FMSet A → List/Rᴸ
 μ = FMS.Rec.f squash/ [ [] ] _∷/_ β
  where
  β : ∀ a b [xs] → a ∷/ b ∷/ [xs] ≡ b ∷/ a ∷/ [xs]
  β a b = elimProp (λ _ → squash/ _ _) (λ xs → eq/ _ _ (γ xs))
   where
     γ : ∀ xs → Rᴸ (a ∷ b ∷ xs) (b ∷ a ∷ xs)
     γ xs = φ (a ∷ b ∷ xs) , η (a ∷ b ∷ xs) , λ c → sym (δ c) ∙ η (a ∷ b ∷ xs) c
      where
      δ : ∀ c → Lcount c (a ∷ b ∷ xs) ≡ Lcount c (b ∷ a ∷ xs)
      δ c with discA c a | discA c b
      δ c | yes _        | yes _ = refl
      δ c | yes _        | no  _ = refl
      δ c | no  _        | yes _ = refl
      δ c | no  _        | no  _ = refl


 -- The inverse is induced by the standard projection of lists into finite multisets,
 -- which is a morphism of count-structures
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
   ρ : ∀ a → Lcount a xs ≡ Lcount a ys
   ρ = λ a → (r .snd .fst a) ∙ sym (r .snd .snd a)

   θ : ∀ a → FMScount discA a (List→FMSet xs) ≡ FMScount discA a (List→FMSet ys)
   θ a = sym (List→FMSet-count a xs) ∙∙ ρ a ∙∙ List→FMSet-count a ys

   path : List→FMSet xs ≡ List→FMSet ys
   path = FMSO.FMScountExt.Thm discA _ _ θ
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


 FMSet≃List/Rᴸ : FMSet A ≃ List/Rᴸ
 FMSet≃List/Rᴸ = isoToEquiv (iso μ ν σ τ)

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
  ∙ There is a bisimulation between lists and the basic data type of the HIT
    with the higher constructors removed (like AList)

 Then we get that this HIT is equivalent to the corresponding set quotient that identifies elements
 that give the same count on each a : A.

 TODO: Show that all the equivalences are indeed isomorphisms of multisets!
 -}
