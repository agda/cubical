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
open import Cubical.Data.Sum
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

π₄S³≅ℤ/something : GroupEquiv ℤGroup (π 3 𝕊²) → Type
π₄S³≅ℤ/something eq =
  GroupIso (π 4 𝕊³)
           (ℤ/ abs (invEq (fst eq) [ ∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂ ]×))

miniLem₁ : Type
miniLem₁ = (g : ℤ) → gen₁-by ℤGroup g → (g ≡ 1) ⊎ (g ≡ -1)

miniLem₂ : Type
miniLem₂ = (ϕ : GroupEquiv ℤGroup ℤGroup) (g : ℤ)
         → (abs g ≡ abs (fst (fst ϕ) g))

-- some minor group lemmas
groupLem-help : miniLem₁
              → (g : ℤ)
              → gen₁-by ℤGroup g
              → (ϕ : GroupHom ℤGroup ℤGroup)
              → (fst ϕ g ≡ pos 1) ⊎ (fst ϕ g ≡ negsuc 0)
              → isEquiv (fst ϕ)
groupLem-help grlem1 g gen ϕ = main (grlem1 g gen)
  where
  isEquiv- : isEquiv (-_)
  isEquiv- = isoToIsEquiv (iso -_ -_ -Involutive -Involutive)

  lem : fst ϕ (pos 1) ≡ pos 1 → fst ϕ ≡ idfun _
  lem p = funExt lem2
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

  lem₂ : fst ϕ (negsuc 0) ≡ pos 1 → fst ϕ ≡ -_
  lem₂ p = funExt lem2
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

  main : (g ≡ pos 1) ⊎ (g ≡ negsuc 0)
      → (fst ϕ g ≡ pos 1) ⊎ (fst ϕ g ≡ negsuc 0)
      → isEquiv (fst ϕ)
  main (inl p) =
    J (λ g p → (fst ϕ g ≡ pos 1)
             ⊎ (fst ϕ g ≡ negsuc 0) → isEquiv (fst ϕ))
      (λ { (inl x) → subst isEquiv (sym (lem x)) (snd (idEquiv _))
         ; (inr x) → subst isEquiv
                            (sym (lem₂ (IsGroupHom.presinv (snd ϕ) (pos 1)
                          ∙ (cong (λ x → pos 0 - x) x))))
                            isEquiv- })
                 (sym p)
  main (inr p) =
    J (λ g p → (fst ϕ g ≡ pos 1)
             ⊎ (fst ϕ g ≡ negsuc 0) → isEquiv (fst ϕ))
      (λ { (inl x) → subst isEquiv (sym (lem₂ x)) isEquiv-
         ; (inr x) → subst isEquiv
                       (sym (lem (
                       IsGroupHom.presinv (snd ϕ) (negsuc 0)
                     ∙ cong (λ x → pos 0 - x) x)))
                    (snd (idEquiv _))})
      (sym p)

groupLem : {G : Group₀}
         → miniLem₁
         → GroupEquiv ℤGroup G
         → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ)
groupLem {G = G} s =

-- snd (fst (BijectionIsoToGroupEquiv {G = G} {H = ℤGroup}
--   (bijIso ϕ
--   (isMono→isInjective ϕ (λ {x} {y} hxy → {!sym (cong (ϕ .fst) (hg x .snd)) ∙ hxy ∙ cong (ϕ .fst) (hg y .snd)!}))
--   λ x → ∣ e .fst .fst x , {!hg (e .fst .fst x)!} ∣))) -- let boo : (a b : fst G) → invEq (e .fst) a ≡ invEq (e .fst) b → a ≡ b
--            --     boo = {!!}
--            -- in hg x .snd ∙ boo _ _ {!!}) {!!})))
  GroupEquivJ
    (λ G _ → (g : fst G)
         → gen₁-by G g
         → (ϕ : GroupHom G ℤGroup)
         → (fst ϕ g ≡ 1) ⊎ (fst ϕ g ≡ -1)
         → isEquiv (fst ϕ))
    (groupLem-help s)

-- summary
module π₄S³
  (mini-lem₁ : miniLem₁)
  (mini-lem₂ : miniLem₂)
  (ℤ≅π₃S² : GroupEquiv ℤGroup (π 3 𝕊²))
  (gen-by-HopfMap : π₃S²-gen)
  (π₄S³≅ℤ/whitehead : π₄S³≅ℤ/something ℤ≅π₃S²)
  (hopfWhitehead : abs (HopfInvariant-π' 0 ([ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)) ≡ 2)
  where
  hopfInvariantEquiv : GroupEquiv (π 3 𝕊²) ℤGroup
  fst (fst hopfInvariantEquiv) = HopfInvariant-π' 0
  snd (fst hopfInvariantEquiv) = {!HopfInvariant-π' 0!}
    -- groupLem mini-lem₁ ℤ≅π₃S² ∣ HopfMap ∣₂
    --          gen-by-HopfMap
    --          (GroupHom-HopfInvariant-π' 0)
    --          (abs→⊎ _ _ HopfInvariant-HopfMap)
  snd hopfInvariantEquiv = snd (GroupHom-HopfInvariant-π' 0)

  lem : ∀ {G : Group₀} (ϕ ψ : GroupEquiv ℤGroup G) (g : fst G)
      → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g)
  lem =
    GroupEquivJ
      (λ G ϕ → (ψ : GroupEquiv ℤGroup G) (g : fst G)
      → abs (invEq (fst ϕ) g) ≡ abs (invEq (fst ψ) g))
      λ ψ → mini-lem₂ (invGroupEquiv ψ)

  main : GroupIso (π 4 𝕊³) (ℤ/ 2)
  main = subst (GroupIso (π 4 𝕊³))
               (cong (ℤ/_) (lem ℤ≅π₃S² (invGroupEquiv (hopfInvariantEquiv)) _ ∙ hopfWhitehead))
               π₄S³≅ℤ/whitehead
