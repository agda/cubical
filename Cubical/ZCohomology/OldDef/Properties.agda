{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.OldDef.Properties where

open import Cubical.ZCohomology.OldDef.Base
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool

open import Cubical.ZCohomology.OldDef.cupProdPrelims renaming (Kn→ΩKn+1 to Kn→ΩKn+1')

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                 (A : Set ℓ) →
                 (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₀
  module coHomRed+1 where
  helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
  helpLemma {C = C} = isoToPath (iso map1
                                     map2
                                     (λ b → linvPf b)
                                     (λ _  → refl))
    where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
    map1 f = map1' , refl module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)

    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
      where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
      helper (inl x) = refl
      helper (inr tt) = sym snd
      
coHomRed+1Equiv (suc n) A i = ∥ coHomRed+1.helpLemma A i {C = ((coHomK (suc n)) , ∣ north ∣)} i ∥₀



-- -------------------
-- {- This section contains a proof of Kn≃ΩKn+1, which is needed for the cup product -}

-- {- Compiles slowly right now. Possible improvements :
-- 1. Use S¹ instead of S 1 in definition of K.
-- 2. Use copatterns -}

-- Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
-- Kn→ΩKn+1 = Kn→ΩKn+1'

-- isEquivKn→ΩKn+1 : (n : ℕ) → isEquiv (Kn→ΩKn+1 n)
-- isEquivKn→ΩKn+1 zero = compEquiv (looper , isEquivLooper) (cong ∣_∣ , isEquivHelper hLevl3) .snd
--   where
--   hLevl3 : (x y : S₊ 1) (p q : x ≡ y) → isProp (p ≡ q)
--   hLevl3 x y = J (λ y p → (q : x ≡ y) → isProp (p ≡ q) )
--                  (transport (λ i → isSet (helper (~ i))) isSetInt refl)
--     where
--     helper : (x ≡ x) ≡ Int
--     helper = (λ i → transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x ≡ transp (λ j → ua S1≃SuspBool (~ j ∨ ~ i)) (~ i) x) ∙
--            (λ i → transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x) ≡ transp (λ j → S¹≡SuspBool (~ j ∨ ~ i)) (~ i) (transport (sym (ua S1≃SuspBool)) x)) ∙
--            basedΩS¹≡Int (transport (sym S¹≡SuspBool) (transport (sym (ua S1≃SuspBool)) x))
-- isEquivKn→ΩKn+1 (suc zero) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn zero (~ i)))
--                                         (compEquiv (trElim (λ _ → isOfHLevelTrunc (2 + (suc zero))) (λ a → ∣ ϕ north a ∣) ,
--                                                      isEquiv∣ϕ∣)
--                                                    (truncEquivΩ (ℕ→ℕ₋₂ (suc zero))) .snd)
-- isEquivKn→ΩKn+1 (suc (suc n)) = transport (λ i → isEquiv (Kn→ΩKn+1Sucn (suc n) (~ i)))
--                                       (compEquiv (connectedTruncEquiv2 (4 + n) _ (ϕ north) (n , λ i → suc (suc (suc (+-suc n n (~ i))))) ?)
--                                                  (truncEquivΩ (ℕ→ℕ₋₂ (suc (suc n)))) .snd)

-- Kn≃ΩKn+1 : (n : ℕ) → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
-- Kn≃ΩKn+1 n = Kn→ΩKn+1 n , isEquivKn→ΩKn+1 n

-- ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
-- ΩKn+1→Kn n a = equiv-proof (isEquivKn→ΩKn+1 n) a .fst .fst
