{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.Summary where

{-
This file contains a summary of what remains for π₄(S³) ≅ ℤ/2ℤ to be proved.
See the module π₄S³ at the end of this file.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int
  renaming (_·_ to _·ℤ_ ; _+_ to _+ℤ_)

open import Cubical.Homotopy.Group.Base hiding (π)
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.Whitehead
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetTruncation

open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Bool to BoolGroup ; Unit to UnitGroup)
open import Cubical.Algebra.Group.ZAction

-- TODO: this should not be off by one in the definition
π : {ℓ : Level} → ℕ → Pointed ℓ → Group ℓ
π n X = π'Gr (predℕ n) X

-- Nicer notation for spheres
𝕊² = S₊∙ 2
𝕊³ = S₊∙ 3

[_]× : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
     → π' (suc n) X × π' (suc m) X → π' (suc (n + m)) X
[_]× (f , g) = [ f ∣ g ]π'

-- Some type abbreviations (unproved results)
π₃S²-gen : Type
π₃S²-gen = gen₁-by (π 3 𝕊²) ∣ HopfMap ∣₂

π₄S³≅ℤ/something : GroupEquiv (π 3 𝕊²) ℤGroup → Type₁
π₄S³≅ℤ/something eq =
  π 4 𝕊³ ≡ ℤ/ abs (eq .fst .fst [ ∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂ ]×)

asdf : (n : ℤ) (m : ℕ) → n ·ℤ negsuc m ≡ - (n ·ℤ pos (suc m))
asdf (pos n) m = pos·negsuc n m
asdf (negsuc n) m = negsuc·negsuc n m ∙ sym (-DistL· (negsuc n) (pos (suc m)))

miniLem₁ : (g : ℤ) → gen₁-by ℤGroup g → (g ≡ 1) ⊎ (g ≡ -1)
miniLem₁ (pos zero) h = ⊥-rec (negsucNotpos 0 0 (h (negsuc 0) .snd ∙ rUnitℤ· ℤGroup _))
miniLem₁ (pos (suc zero)) h = inl refl
miniLem₁ (pos (suc (suc n))) h = ⊥-rec (¬1=x·suc-suc n _ (rem (pos 1)))
  where
  rem : (x : ℤ) → x ≡ fst (h x) ·ℤ pos (suc (suc n))
  rem x = h x .snd ∙ sym (ℤ·≡· (fst (h x)) (pos (suc (suc n))))
miniLem₁ (negsuc zero) h = inr refl
miniLem₁ (negsuc (suc n)) h = ⊥-rec (¬1=x·suc-suc n _ (rem (pos 1) ∙ asdf (fst (h (pos 1))) (suc n) ∙ -DistL· _ _))
  where
  rem : (x : ℤ) → x ≡ fst (h x) ·ℤ negsuc (suc n)
  rem x = h x .snd ∙ sym (ℤ·≡· (fst (h x)) (negsuc (suc n)))

lem : (ϕ : GroupHom ℤGroup ℤGroup) → fst ϕ (pos 1) ≡ pos 1 → fst ϕ ≡ idfun _
lem ϕ p = funExt lem2
    where
    lem₁ : (x₁ : ℕ) → fst ϕ (pos x₁) ≡ idfun ℤ (pos x₁)
    lem₁ zero = IsGroupHom.pres1 (snd ϕ)
    lem₁ (suc zero) = p
    lem₁ (suc (suc n)) =
      IsGroupHom.pres· (snd ϕ) (pos (suc n)) 1
                             ∙ cong₂ _+ℤ_ (lem₁ (suc n)) p

    lem2 : (x₁ : ℤ) → fst ϕ x₁ ≡ idfun ℤ x₁
    lem2 (pos n) = lem₁ n
    lem2 (negsuc zero) =
      IsGroupHom.presinv (snd ϕ) 1 ∙ cong (λ x → pos 0 - x) p
    lem2 (negsuc (suc n)) =
        (cong (fst ϕ) (sym (+Comm (pos 0) (negsuc (suc n))))
      ∙ IsGroupHom.presinv (snd ϕ) (pos (suc (suc n))))
      ∙∙ +Comm (pos 0) _
      ∙∙ cong (-_) (lem₁ (suc (suc n)))

lem₂ : (ϕ : GroupHom ℤGroup ℤGroup) → fst ϕ (negsuc 0) ≡ pos 1 → fst ϕ ≡ -_
lem₂ ϕ p = funExt lem2
    where
    s = IsGroupHom.presinv (snd ϕ) (negsuc 0)
     ∙∙ +Comm (pos 0) _
     ∙∙ cong -_ p

    lem2 : (n : ℤ) → fst ϕ n ≡ - n
    lem2 (pos zero) = IsGroupHom.pres1 (snd ϕ)
    lem2 (pos (suc zero)) = s
    lem2 (pos (suc (suc n))) =
         IsGroupHom.pres· (snd ϕ) (pos (suc n)) 1
       ∙ cong₂ _+ℤ_ (lem2 (pos (suc n))) s
    lem2 (negsuc zero) = p
    lem2 (negsuc (suc n)) =
         IsGroupHom.pres· (snd ϕ) (negsuc n) (negsuc 0)
       ∙ cong₂ _+ℤ_ (lem2 (negsuc n)) p


foo1 : (ϕ : GroupEquiv ℤGroup ℤGroup) → (fst (fst ϕ) (pos 1) ≡ pos 1) ⊎ (fst (fst ϕ) (pos 1) ≡ - (pos 1))
foo1 ϕ =
  groupEquivPresGen ℤGroup (compGroupEquiv ϕ (invGroupEquiv ϕ)) (pos 1) (inl (funExt⁻ (cong fst (invEquiv-is-rinv (ϕ .fst))) (pos 1))) ϕ

foo : (ϕ : GroupEquiv ℤGroup ℤGroup) → (g : ℤ) → (fst (fst ϕ) g ≡ g) ⊎ (fst (fst ϕ) g ≡ - g)
foo ϕ g = ⊎-rec (λ h → inl (funExt⁻ (lem (_ , ϕ .snd) h) g))
                (λ h → inr (funExt⁻ (lem₂ (_ , ϕ .snd) (IsGroupHom.presinv (snd ϕ) (pos 1) ∙ sym (pos0+ (- fst (fst ϕ) (pos 1))) ∙ cong -_ h)) g)) (foo1 ϕ)

miniLem₂ : (ϕ : GroupEquiv ℤGroup ℤGroup) (g : ℤ)
         → (abs g ≡ abs (fst (fst ϕ) g))
miniLem₂ ϕ g = ⊎-rec (λ h → sym (cong abs h)) (λ h → sym (abs- _) ∙ sym (cong abs h)) (foo ϕ g)

-- some minor group lemmas
groupLem-help : (g : ℤ)
              → gen₁-by ℤGroup g
              → (ϕ : GroupHom ℤGroup ℤGroup)
              → (fst ϕ g ≡ pos 1) ⊎ (fst ϕ g ≡ negsuc 0)
              → isEquiv (fst ϕ)
groupLem-help g gen ϕ = main (miniLem₁ g gen)
  where
  isEquiv- : isEquiv (-_)
  isEquiv- = isoToIsEquiv (iso -_ -_ -Involutive -Involutive)

  main : (g ≡ pos 1) ⊎ (g ≡ negsuc 0)
      → (fst ϕ g ≡ pos 1) ⊎ (fst ϕ g ≡ negsuc 0)
      → isEquiv (fst ϕ)
  main (inl p) =
    J (λ g p → (fst ϕ g ≡ pos 1)
             ⊎ (fst ϕ g ≡ negsuc 0) → isEquiv (fst ϕ))
      (λ { (inl x) → subst isEquiv (sym (lem ϕ x)) (snd (idEquiv _))
         ; (inr x) → subst isEquiv
                            (sym (lem₂ ϕ (IsGroupHom.presinv (snd ϕ) (pos 1)
                          ∙ (cong (λ x → pos 0 - x) x))))
                            isEquiv- })
                 (sym p)
  main (inr p) =
    J (λ g p → (fst ϕ g ≡ pos 1)
             ⊎ (fst ϕ g ≡ negsuc 0) → isEquiv (fst ϕ))
      (λ { (inl x) → subst isEquiv (sym (lem₂ ϕ x)) isEquiv-
         ; (inr x) → subst isEquiv
                       (sym (lem ϕ (
                       IsGroupHom.presinv (snd ϕ) (negsuc 0)
                     ∙ cong (λ x → pos 0 - x) x)))
                    (snd (idEquiv _))})
      (sym p)

groupLem : {G : Group₀}
         → GroupEquiv ℤGroup G
         → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ)
groupLem {G = G} =
  GroupEquivJ
    (λ G _ → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ))
    groupLem-help

lemabs : ∀ {G : Group₀} (ϕ ψ : GroupEquiv ℤGroup G) (g : fst G)
    → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g)
lemabs =
  GroupEquivJ
    (λ G ϕ → (ψ : GroupEquiv ℤGroup G) (g : fst G)
    → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g))
    λ ψ → miniLem₂ (invGroupEquiv ψ)

-- summary
module π₄S³
  (ℤ≅π₃S² : GroupEquiv (π 3 𝕊²) ℤGroup)
  (gen-by-HopfMap : π₃S²-gen)
  (π₄S³≅ℤ/whitehead : π₄S³≅ℤ/something ℤ≅π₃S²)
  (hopfWhitehead : abs (HopfInvariant-π' 0 ([ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)) ≡ 2)
  where
  hopfInvariantEquiv : GroupEquiv (π 3 𝕊²) ℤGroup
  fst (fst hopfInvariantEquiv) = HopfInvariant-π' 0
  snd (fst hopfInvariantEquiv) =
    groupLem (invGroupEquiv ℤ≅π₃S²) ∣ HopfMap ∣₂
             gen-by-HopfMap
             (GroupHom-HopfInvariant-π' 0)
             (abs→⊎ _ _ HopfInvariant-HopfMap)
  snd hopfInvariantEquiv = snd (GroupHom-HopfInvariant-π' 0)

  main : π 4 𝕊³ ≡ ℤ/ 2
  main = π₄S³≅ℤ/whitehead
       ∙ cong (ℤ/_) (lemabs (invGroupEquiv ℤ≅π₃S²) (invGroupEquiv hopfInvariantEquiv) _ ∙ hopfWhitehead)
