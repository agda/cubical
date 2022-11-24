{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Gysin where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Cohomology.EilenbergMacLane.EilenbergSteenrod
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Sn

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.Algebra.CommRing
open RingStr renaming (_+_ to _+r_)
open PlusBis

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.HITs.Truncation as TR


EM→ΩEM+1-gen : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (suc n))
  → EM G n → x ≡ x
EM→ΩEM+1-gen n x p =
     sym (rUnitₖ (suc n) x)
  ∙∙ cong (x +ₖ_) (EM→ΩEM+1 n p)
  ∙∙ rUnitₖ (suc n) x

ΩEM+1-gen→EM-0ₖ :  ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : _)
  → ΩEM+1→EM-gen {G = G} n (0ₖ (suc n)) x
  ≡ ΩEM+1→EM n x
ΩEM+1-gen→EM-0ₖ zero p = refl
ΩEM+1-gen→EM-0ₖ (suc n) p = refl

EM→ΩEM+1-gen-0ₖ : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : _)
  → EM→ΩEM+1-gen {G = G} n (0ₖ (suc n)) x
  ≡ EM→ΩEM+1 n x
EM→ΩEM+1-gen-0ₖ zero x = sym (rUnit _) ∙ λ j i → lUnitₖ 1 (EM→ΩEM+1 zero x i) j
EM→ΩEM+1-gen-0ₖ (suc n) x = sym (rUnit _) ∙ λ j i → lUnitₖ (suc (suc n)) (EM→ΩEM+1 (suc n) x i) j

EM→ΩEM+1→EM-gen : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (suc n))
  → (y : EM G n) → ΩEM+1→EM-gen n x (EM→ΩEM+1-gen n x y) ≡ y
EM→ΩEM+1→EM-gen {G = G} n =
  EM-raw'-elim _ _ (λ _ → isOfHLevelΠ (suc (suc n))
                   (λ _ → isOfHLevelPath (suc (suc n))
                   (hLevelEM _ n) _ _))
   (EM-raw'-trivElim _ n (λ _ → isOfHLevelΠ (suc n) λ _ → hLevelEM _ n _ _)
     λ y → cong (λ p → ΩEM+1→EM-gen n p (EM→ΩEM+1-gen n p y)) (EM-raw'→EM∙ G (suc n))
          ∙ (λ i → ΩEM+1-gen→EM-0ₖ n (EM→ΩEM+1-gen-0ₖ n y i) i)
          ∙ Iso.leftInv (Iso-EM-ΩEM+1 n) y)

ΩEM+1→EM→ΩEM+1-gen : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (suc n))
  → (y : x ≡ x)
  → EM→ΩEM+1-gen n x (ΩEM+1→EM-gen n x y) ≡ y
ΩEM+1→EM→ΩEM+1-gen n =
  EM-raw'-elim _ _ (λ _ → isOfHLevelΠ (suc (suc n))
                   (λ _ → isOfHLevelPath (suc (suc n))
                   (hLevelEM _ (suc n) _ _) _ _))
   (EM-raw'-trivElim _ n (λ _ → isOfHLevelΠ (suc n) λ _ → hLevelEM _ (suc n) _ _ _ _)
   (subst (λ p → (y : p ≡ p) → EM→ΩEM+1-gen n p (ΩEM+1→EM-gen n p y) ≡ y)
     (sym (EM-raw'→EM∙ _ (suc n)))
     λ p → (λ i → EM→ΩEM+1-gen-0ₖ n (ΩEM+1-gen→EM-0ₖ n p i) i)
          ∙ Iso.rightInv (Iso-EM-ΩEM+1 n) p))


Iso-EM-ΩEM+1-gen : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (suc n))
  → Iso (EM G n) (x ≡ x)
Iso.fun (Iso-EM-ΩEM+1-gen n x) = EM→ΩEM+1-gen n x
Iso.inv (Iso-EM-ΩEM+1-gen n x) = ΩEM+1→EM-gen n x
Iso.rightInv (Iso-EM-ΩEM+1-gen n x) = ΩEM+1→EM→ΩEM+1-gen n x
Iso.leftInv (Iso-EM-ΩEM+1-gen n x) = EM→ΩEM+1→EM-gen n x

ΩEM+1→EM-gen-refl : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ) (x : EM G (suc n))
  → ΩEM+1→EM-gen n x refl ≡ 0ₖ n
ΩEM+1→EM-gen-refl {G = G} n =
  EM-raw'-elim _ (suc n)
    (λ _ → isOfHLevelPath (suc (suc n)) (hLevelEM _ n) _ _)
    (EM-raw'-trivElim _ n
      (λ _ → hLevelEM _ n _ _)
      (lem n))
  where
  lem : (n : ℕ) → ΩEM+1→EM-gen n
    (EM-raw'→EM G (suc n) (snd (EM-raw'∙ G (suc n)))) refl
    ≡ 0ₖ n
  lem zero = ΩEM+1→EM-refl 0
  lem (suc n) = ΩEM+1→EM-refl (suc n)


hLev-map : (G : AbGroup ℓ) (n : ℕ) → isSet (S₊∙ n →∙ EM∙ G n)
hLev-map G n =
  subst isSet (sym (help n)
            ∙ isoToPath (invIso (IsoSphereMapΩ n)))
    (AbGroupStr.is-set (snd G))
  where
  help : (n : ℕ) → fst ((Ω^ n) (EM∙ G n)) ≡ fst G
  help zero = refl
  help (suc n) =
      cong fst (flipΩPath n)
    ∙ cong (fst ∘ (Ω^ n))
       (ua∙ (isoToEquiv (invIso (Iso-EM-ΩEM+1 n)))
            (ΩEM+1→EM-refl n))
    ∙ help n



gen-HⁿSⁿ : (R : Ring ℓ) (n : ℕ)
  → (S₊∙ n →∙ EM∙ (Ring→AbGroup  R) n)
fst (gen-HⁿSⁿ R zero) false = 1r (snd R)
fst (gen-HⁿSⁿ R zero) true = 0ₖ {G = Ring→AbGroup R} 0
snd (gen-HⁿSⁿ R zero) = refl
fst (gen-HⁿSⁿ R (suc zero)) base = 0ₖ 1
fst (gen-HⁿSⁿ R (suc zero)) (loop i) = emloop (1r (snd R)) i
fst (gen-HⁿSⁿ R (suc (suc n))) north = 0ₖ (2 + n)
fst (gen-HⁿSⁿ R (suc (suc n))) south = 0ₖ (2 + n)
fst (gen-HⁿSⁿ R (suc (suc n))) (merid a i) =
  EM→ΩEM+1 (suc n) (gen-HⁿSⁿ R (suc n) .fst a) i
snd (gen-HⁿSⁿ R (suc zero)) = refl
snd (gen-HⁿSⁿ R (suc (suc n))) = refl

desuspHⁿSⁿ : (G : AbGroup ℓ) (n : ℕ)
  → (S₊∙ (suc n) →∙ EM∙ G (suc n)) → (S₊∙ n →∙ EM∙ G n)
fst (desuspHⁿSⁿ G zero f) = λ {false → ΩEM+1→EM-gen 0 _ (cong (fst f) loop)
                             ; true → AbGroupStr.0g (snd G)}
fst (desuspHⁿSⁿ G (suc n) f) x = ΩEM+1→EM-gen (suc n) _ (cong (fst f) (toSusp (S₊∙ (suc n)) x))
snd (desuspHⁿSⁿ G zero f) = refl
snd (desuspHⁿSⁿ G (suc n) f) =
    cong (ΩEM+1→EM-gen (suc n) _) (cong (cong (fst f)) (rCancel (merid (ptSn (suc n)))))
  ∙ (λ i → ΩEM+1→EM-gen (suc n) _ (refl {x = snd f i}))
  ∙ ΩEM+1→EM-refl (suc n)

untrunc-HⁿSⁿ : (G : AbGroup ℓ) (n : ℕ)
  → (S₊∙ n →∙ EM∙ G n) ≃ (fst G)
untrunc-HⁿSⁿ G zero =
  isoToEquiv
    (iso (λ f → fst f false)
         (λ g → (λ {true → _ ; false → g}) , refl)
         (λ g → refl)
         λ g → Σ≡Prop (λ _ → AbGroupStr.is-set (snd G) _ _)
                       (funExt λ { false → refl ; true → sym (snd g)}))
untrunc-HⁿSⁿ G (suc n) =
    compEquiv
    (invEquiv
      (compEquiv (fst (coHom≅coHomRed n G (S₊∙ (suc n))))
      (isoToEquiv (setTruncIdempotentIso (hLev-map G (suc n))))))
    (fst (Hⁿ[Sⁿ,G]≅G G n))

untrunc-HⁿSⁿ-ind : (G : AbGroup ℓ) (n : ℕ)
  → (f : S₊∙ (suc n) →∙ EM∙ G (suc n))
  → untrunc-HⁿSⁿ G (suc n) .fst f
   ≡ untrunc-HⁿSⁿ G n .fst (desuspHⁿSⁿ G n f)
untrunc-HⁿSⁿ-ind G zero f = refl
untrunc-HⁿSⁿ-ind G (suc n) f = refl

gen-HⁿSⁿ↦1 : (R : Ring ℓ) (n : ℕ)
  → untrunc-HⁿSⁿ (Ring→AbGroup R) n .fst (gen-HⁿSⁿ R n) ≡ 1r (snd R)
gen-HⁿSⁿ↦1 R zero = refl
gen-HⁿSⁿ↦1 R (suc zero) = transportRefl _
                        ∙ +IdL (snd R) (1r (snd R))
gen-HⁿSⁿ↦1 R (suc (suc n)) =
    cong (fst (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup R) n) .fst)
      (cong ∣_∣₂ (funExt λ x
        → (cong (ΩEM+1→EM (suc n)) (cong-∙ (fst (gen-HⁿSⁿ R (suc (suc n)))) (merid x) (sym (merid (ptSn (suc n)))))
        ∙ ΩEM+1→EM-hom (suc n) _ _)
        ∙ cong₂ _+ₖ_ (Iso.leftInv (Iso-EM-ΩEM+1 (suc n))
                        (gen-HⁿSⁿ R (suc n) .fst x))
                     (((λ i → ΩEM+1→EM-sym (suc n) (EM→ΩEM+1 (suc n) (snd (gen-HⁿSⁿ R (suc n)) i)) i)
                     ∙ cong -ₖ_ (Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) (0ₖ (suc n)))
                     ∙ -0ₖ (suc n)))
        ∙ rUnitₖ (suc n) _))
  ∙ gen-HⁿSⁿ↦1 R (suc n)

untrunc-HⁿSⁿ-inv : (R : Ring ℓ) (n : ℕ)
  → fst R → (S₊∙ n →∙ EM∙ (Ring→AbGroup R) n)
fst (untrunc-HⁿSⁿ-inv R n r) x =
  subst (EM (Ring→AbGroup R)) (+'-comm n 0)
    (_⌣ₖ_ {n = n} {m = 0} (fst (gen-HⁿSⁿ R n) x) r)
snd (untrunc-HⁿSⁿ-inv R n r) =
  cong (subst (EM (Ring→AbGroup R)) (+'-comm n 0))
        (cong (_⌣ₖ r) (snd (gen-HⁿSⁿ R n))
       ∙ 0ₖ-⌣ₖ n 0 r)
       ∙ λ j → transp (λ i → EM (Ring→AbGroup R)
                               (+'-comm n 0 (i ∨ j)))
                     j (0ₖ (+'-comm n 0 j))

perhaps : (R : Ring ℓ) (n : ℕ) (r : fst R) →
      ((fst (untrunc-HⁿSⁿ (Ring→AbGroup R) n))
     ∘ untrunc-HⁿSⁿ-inv R n) r
     ≡ r
perhaps R zero r = transportRefl _ ∙ ·IdL (snd R) r
perhaps R (suc zero) r =
    transportRefl _
  ∙ transportRefl _
  ∙ cong₂ (_+r_ (snd R)) (transportRefl (0r (snd R)))
                         (transportRefl _
                       ∙ ·IdL (snd R) r)
  ∙ +IdL (snd R) r
perhaps R (suc (suc n)) r =
    untrunc-HⁿSⁿ-ind (Ring→AbGroup R) (suc n) _ ∙
    (cong (fst (untrunc-HⁿSⁿ (Ring→AbGroup R) (suc n)))
          (→∙Homogeneous≡
            (isHomogeneousEM _)
            (funExt λ z →
              cong (ΩEM+1→EM (suc n)) (lem z)
            ∙ Iso-EM-ΩEM+1 (suc n) .Iso.leftInv (subst (EM (Ring→AbGroup R))
              (+'-comm (suc n) 0) (_⌣ₖ_ {m = 0} (fst (gen-HⁿSⁿ R (suc n)) z) r)))))
  ∙ perhaps R (suc n) r
  where
  lem : (z : _) → (λ i → subst (EM (Ring→AbGroup R)) (+'-comm (suc (suc n)) 0)
         (fst (gen-HⁿSⁿ R (suc (suc n))) (toSusp (S₊∙ (suc n)) z i) ⌣ₖ r))
         ≡ EM→ΩEM+1 (suc n) (subst (EM (Ring→AbGroup R))
            (+'-comm (suc n) 0) (_⌣ₖ_ {m = 0} (fst (gen-HⁿSⁿ R (suc n)) z) r))
  lem z = ((λ j → transp (λ i → typ (Ω (EM∙ (Ring→AbGroup R)
                          (+'-comm (suc (suc n)) 0 (~ j ∨ i))))) (~ j)
            λ i → transp (λ i → EM (Ring→AbGroup R)
                          (+'-comm (suc (suc n)) 0 (~ j ∧ i)))
                          j
                          (fst (gen-HⁿSⁿ R (suc (suc n)))
                           (toSusp (S₊∙ (suc n)) z i) ⌣ₖ r))
         ∙ (λ j → transport (λ i → typ (Ω (EM∙ (Ring→AbGroup R)
                    (isSetℕ (suc (suc n)) (suc (suc n))
                      (+'-comm (suc (suc n)) 0) refl j i))))
                    λ i → _⌣ₖ_ {n = suc (suc n)} {m = zero}
                           (fst (gen-HⁿSⁿ R (suc (suc n)))
                            (toSusp (S₊∙ (suc n)) z i)) r)
         ∙ transportRefl _
         ∙ cong (cong (λ x → _⌣ₖ_ {n = suc (suc n)} {m = zero} x r))
                (cong-∙ (fst (gen-HⁿSⁿ R (suc (suc n))))
                  (merid z) (sym (merid (ptSn (suc n))))
              ∙ cong₂ _∙_ refl
                 (cong sym (cong (EM→ΩEM+1 (suc n))
                           (gen-HⁿSⁿ R (suc n) .snd)
                       ∙ EM→ΩEM+1-0ₖ (suc n)))
              ∙ sym (rUnit _))
         ∙ sym (EM→ΩEM+1-distr⌣ₖ0 n (gen-HⁿSⁿ R (suc n) .fst z) r))
        ∙ cong (EM→ΩEM+1 (suc n))
           (sym (transportRefl _)
          ∙ λ i → subst (EM (Ring→AbGroup R))
                   (isSetℕ (suc n) (suc n) refl (+'-comm (suc n) 0) i)
                   (_⌣ₖ_ {m = 0} (fst (gen-HⁿSⁿ R (suc n)) z) r))

isEq-inv : (R : Ring ℓ) (n : ℕ)
  → isEquiv (untrunc-HⁿSⁿ-inv R n)
isEq-inv R n =
  composesToId→Equiv _ _ (funExt (perhaps R n))
    (untrunc-HⁿSⁿ (Ring→AbGroup R) n .snd)

module pre-Thom (R' : CommRing ℓ'') where
  R = CommRing→Ring R'
  RR = (CommRing→AbGroup R')
  EMR = EM (CommRing→AbGroup R')
  EMR∙ = EM∙ (CommRing→AbGroup R')

  substEMR : {n m : ℕ} (p : n ≡ m) → subst EMR p (0ₖ n) ≡ 0ₖ m
  substEMR {n = n} =
    J (λ m p → subst EMR p (0ₖ n) ≡ 0ₖ m) (transportRefl _)

  g-comm : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (n +' i)
  fst (g-comm n i x) y = gen-HⁿSⁿ R n .fst y ⌣ₖ x
  snd (g-comm n i x) =
      cong (_⌣ₖ x) (gen-HⁿSⁿ R n .snd)
    ∙ 0ₖ-⌣ₖ n i x

  pre-g : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (i +' n)
  fst (pre-g n i x) y = x ⌣ₖ gen-HⁿSⁿ R n .fst y
  snd (pre-g n i x) =
    cong (x ⌣ₖ_) (gen-HⁿSⁿ R n .snd)
      ∙ ⌣ₖ-0ₖ i n x

  g-cute : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (i + n)
  g-cute n i x = (subst EMR (+'≡+ i n) , substEMR (+'≡+ i n)) ∘∙ pre-g n i x

  indexIso₁ : (n i : ℕ) → EMR∙ (i + n) ≃∙ EMR∙ (n + i)
  fst (indexIso₁ n i) = substEquiv EMR (+-comm i n)
  snd (indexIso₁ n i) = substEMR (+-comm i n)

  indexIso₂ : (n i : ℕ) → EMR∙ (n + i) ≃∙ EMR∙ (n +' i)
  fst (indexIso₂ n i) = substEquiv EMR (sym (+'≡+ n i))
  snd (indexIso₂ n i) = substEMR (sym (+'≡+ n i))

  -ₖ^-iso : ∀ {ℓ} {G : AbGroup ℓ} {k : ℕ} (n m : ℕ) → Iso (EM G k) (EM G k)
  Iso.fun (-ₖ^-iso n m) = -ₖ^[ n · m ]
  Iso.inv (-ₖ^-iso n m) = -ₖ^[ n · m ]
  Iso.rightInv (-ₖ^-iso n m) = -ₖ^< n · m >² _ _ _
  Iso.leftInv (-ₖ^-iso n m) = -ₖ^< n · m >² _ _ _

  g-cute' : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (n +' i)
  g-cute' n i =
      Iso.fun (pre∘∙equiv
                (compEquiv∙ (isoToEquiv (-ₖ^-iso i n) , -ₖ^<_·_>∙ i n _ _ _)
                (compEquiv∙ (indexIso₁ n i) (indexIso₂ n i))))
    ∘ g-cute n i

  g-cute≡ : (n i : ℕ) → g-cute' n i ≡ g-comm n i
  g-cute≡ n i = funExt (λ x → →∙Homogeneous≡ (isHomogeneousEM (n +' i))
    (funExt λ y → cong (subst EMR (sym (+'≡+ n i)))
                    (cong (subst EMR (+-comm i n))
                      ((cong (-ₖ^[ i · n ])
                          (cong (subst EMR (+'≡+ i n))
                            (⌣ₖ-comm {G'' = R'} i n x (gen-HⁿSⁿ R n .fst y))))))
                 ∙ killTransp EMR -ₖ^[ i · n ] _
                    (λ _ x → -ₖ^< i · n >² _ _ _ x) _
                    (+'-comm n i)  _ _ _ _ _
                    (gen-HⁿSⁿ R n .fst y ⌣ₖ x)))
    where
    killTransp : (A : ℕ → Type ℓ) (-ₖ_ : {n : ℕ} → A n → A n) (a : ℕ)
      → ((n : ℕ) → (x : A n) → -ₖ (-ₖ x) ≡ x)
      → (b : ℕ)
      → (p : a ≡ b) (c : ℕ) (q : b ≡ c) (d : ℕ) (r : c ≡ d) (s : d ≡ a)
      → (base : A a)
      → subst A s (subst A r (-ₖ subst A q (subst A p (-ₖ base)))) ≡ base
    killTransp A f i a = J> (J> (J> λ p b
      → cong (subst A p) (transportRefl _ ∙ cong f (transportRefl _ ∙ transportRefl _)
         ∙ a _ b)
      ∙ (λ i → subst A (isSetℕ _ _ p refl i) b)
      ∙ transportRefl b))

  isEquivBiImpl : (n i : ℕ) → (isEquiv (g-comm n i) → isEquiv (g-cute n i))
                             × (isEquiv (g-cute n i) → isEquiv (g-comm n i))
  fst (isEquivBiImpl n i) eq = 
    subst isEquiv
      (funExt (λ x → secEq e (g-cute n i x)))
    (compEquiv  (_ , subst isEquiv (sym (g-cute≡ n i)) eq) e .snd)
    where
    e = isoToEquiv (invIso (pre∘∙equiv
                (compEquiv∙ (isoToEquiv (-ₖ^-iso i n) , -ₖ^<_·_>∙ i n _ _ _)
                (compEquiv∙ (indexIso₁ n i) (indexIso₂ n i)))))
  snd (isEquivBiImpl n i) eq =
    subst isEquiv (g-cute≡ n i)
      (compEquiv
        (_ , eq)
        (isoToEquiv (pre∘∙equiv
        (compEquiv∙ (isoToEquiv (-ₖ^-iso i n) , -ₖ^<_·_>∙ i n _ _ _)
        (compEquiv∙ (indexIso₁ n i) (indexIso₂ n i))))) .snd)

  isEquiv-lem : (n i : ℕ) → isEquiv (cong {x = 0ₖ (suc i)} {y = 0ₖ (suc i)} (g-cute n (suc i)))
    → (x y : EMR (suc i))
    → isEquiv (cong {x = x} {y = y} (g-cute n (suc i)))
  isEquiv-lem n i p =
    EM→Prop (Ring→AbGroup R) i (λ _ → isPropΠ λ _ → isPropIsEquiv _)
      (EM→Prop (Ring→AbGroup R) i (λ _ → isPropIsEquiv _)
        p)

  eq' : (n i : ℕ) (f : S₊∙ n →∙ EMR∙ (suc (i + n)))
     → Iso (f ≡ f)
            (S₊∙ n →∙ EMR∙ (i + n))
  fst (Iso.fun (eq' n i f) st) x =
    ΩEM+1→EM-gen (i + n) _ (funExt⁻ (cong fst st) x)
  snd (Iso.fun (eq' n i f) st) =
      (λ j → ΩEM+1→EM-gen (i + n) (snd f j) λ i → snd (st i) j)
    ∙ ΩEM+1→EM-gen-refl (i + n) _
  Iso.inv (eq' n i f) st = ΣPathP ((funExt (λ x → EM→ΩEM+1-gen _ (fst f x) (fst st x)))
                               , flipSquare ((λ j → EM→ΩEM+1-gen (i + n) (snd f j) (snd st j))
                                           ▷ (EM→ΩEM+1-gen-0ₖ (i + n) _
                                           ∙ EM→ΩEM+1-0ₖ (i + n))))
  Iso.rightInv (eq' n i f) st =
    →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ x → Iso.leftInv (Iso-EM-ΩEM+1-gen (i + n) (fst f x)) (st .fst x))
  Iso.leftInv (eq' n i f) st =
    →∙HomogeneousSquare (isHomogeneousEM _)
      refl refl (Iso.inv (eq' n i f) (Iso.fun (eq' n i f) st)) st
      (cong funExt (funExt λ x → Iso.rightInv (Iso-EM-ΩEM+1-gen (i + n) (fst f x)) λ i → st i .fst x))

  g-cute-ind : (n i : ℕ) → g-cute n i
                        ≡ Iso.fun (eq' n i (g-cute n (suc i) (0ₖ (suc i))))
                         ∘ cong {x = 0ₖ (suc i)} {y = 0ₖ (suc i)} (g-cute n (suc i))
                         ∘ EM→ΩEM+1 i
  g-cute-ind zero zero =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM {G = Ring→AbGroup R} 0)
      (funExt λ y → transportRefl _
        ∙ sym ((λ j → ΩEM+1→EM 0
               (λ i → transportRefl (_⌣ₖ_ {n = 1} {m = 0}
                       (EM→ΩEM+1 0 x i)
                       (gen-HⁿSⁿ R zero .fst y)) j))
             ∙ Iso.leftInv (Iso-EM-ΩEM+1 0)
                (_⌣ₖ_ {n = 0} {m = 0} x (gen-HⁿSⁿ R zero .fst y))))
  g-cute-ind zero (suc i) =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y → sym (cong (ΩEM+1→EM (suc i + zero))
                           (cong (cong (subst EMR (cong suc (+'≡+ (suc i) zero))))
                             (sym (EM→ΩEM+1-distr⌣ₖ0 i x (gen-HⁿSⁿ R zero .fst y))))
                       ∙∙ (λ j → transp (λ s → EMR (+'≡+ (suc i) zero (s ∨ ~ j))) (~ j)
                                   (ΩEM+1→EM (+'≡+ (suc i) zero (~ j))
                                     λ k → transp (λ s → EMR (suc (+'≡+ (suc i) zero (s ∧ ~ j))))
                                       j
                                       (EM→ΩEM+1 (suc i) (_⌣ₖ_ {n = suc i} {m = zero}
                                         x (gen-HⁿSⁿ R zero .fst y)) k)))
                       ∙∙ cong (subst EMR (λ i₁ → suc (+-zero i (~ i₁))))
                           (Iso.leftInv (Iso-EM-ΩEM+1 (suc i)) _)))
  g-cute-ind (suc n) zero = funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y
      → transportRefl _
      ∙ sym (cong (ΩEM+1→EM (suc n))
              ((λ k j → subst EMR (+'≡+ (suc zero) (suc n))
                (sym (EM→ΩEM+1-distr⌣ₖ0n n x (gen-HⁿSⁿ R (suc n) .fst y)) k j))
            ∙ (λ j → transp (λ i → Ω (EMR∙ (+'≡+ (suc zero) (suc n) (i ∨ j))) .fst)
                            (~ j)
                      λ k → transp (λ i → EMR (+'≡+ (suc zero) (suc n) (i ∨ ~ j)))
                        j (EM→ΩEM+1 (suc n) (x ⌣[ R , 0 , (suc n) ]ₖ gen-HⁿSⁿ R (suc n) .fst y) k))
            ∙ (λ j → subst (λ n → Ω (EMR∙ n) .fst)
                       (isSetℕ (suc (suc n)) (suc (suc n)) (+'≡+ (suc zero) (suc n)) refl j)
                        (EM→ΩEM+1 (suc n) (x ⌣[ R , 0 , (suc n) ]ₖ gen-HⁿSⁿ R (suc n) .fst y)))
            ∙ transportRefl _)
           ∙ Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) _))
  g-cute-ind (suc n) (suc i) =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y
      → sym ((cong (ΩEM+1→EM (suc i + suc n)))
               (cong (cong (subst EMR (+'≡+ (suc (suc i)) (suc n))))
                 (sym (EM→ΩEM+1-distr⌣ₖ i n x (gen-HⁿSⁿ R (suc n) .fst y))))
           ∙ (λ j → transp (λ s → EMR (suc (+-suc i n (j ∧ ~ s)))) (~ j)
                      ((ΩEM+1→EM (suc (+-suc i n j))
                        (λ k → transp (λ s → EMR (suc (suc (+-suc i n (~ s ∨ j)))))
                          j (EM→ΩEM+1 (suc (suc (i + n)))
                           (x ⌣ₖ gen-HⁿSⁿ R (suc n) .fst y) k)))))
           ∙ cong (subst EMR (λ i₁ → suc (+-suc i n (~ i₁))))
              (Iso.leftInv (Iso-EM-ΩEM+1 (suc i +' suc n))
                (x ⌣ₖ gen-HⁿSⁿ R (suc n) .fst y))))

  g-ind-main : (n i : ℕ) → isEquiv (g-cute n i) → isEquiv (g-cute n (suc i))
  g-ind-main n i eq =
    isEmbedding×isSurjection→isEquiv
      ((λ x y → isEquiv-lem n i
                  (subst isEquiv (sym help)
                    (myEq .snd))
                  x y)
      , λ f → PT.map
          (λ p → subst (fiber (g-cute n (suc i))) (sym p)
            ((0ₖ (suc i)) , (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ x → cong (subst EMR (+'≡+ (suc i) n))
                              (0ₖ-⌣ₖ (suc i) n (gen-HⁿSⁿ R n .fst x))
                           ∙ substEMR (+'≡+ (suc i) n)))))
          (Iso.fun PathIdTrunc₀Iso
            (isContr→isProp (help2 i n) ∣ f ∣₂ (0ₕ∙ _))))
    where
    myEq = compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 i)))
             (compEquiv (g-cute n i , eq)
               (isoToEquiv (invIso (eq' n i (g-cute n (suc i) (0ₖ (suc i)))))))

    help : cong (g-cute n (suc i))
         ≡ myEq .fst
    help = funExt (λ p → sym (Iso.leftInv (eq' n i (g-cute n (suc i) (0ₖ (suc i)))) _
                        ∙ cong (cong (g-cute n (suc i)))
                           (Iso.rightInv (Iso-EM-ΩEM+1 i) _)))
         ∙ sym (cong (λ f → Iso.inv (eq' n i (g-cute n (suc i) (0ₖ (suc i))))
                     ∘ f ∘ ΩEM+1→EM i)
               (g-cute-ind n i))
    
    help2 : (i n : ℕ) → isContr (∥ S₊∙ n →∙ EMR∙ (suc (i + n)) ∥₂)
    help2 i zero = 0ₕ∙ _
      , ST.elim
          (λ _ → isSetPathImplicit)
          λ f → TR.rec (isProp→isOfHLevelSuc (i + zero) (squash₂ _ _))
            (λ p → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ { false → sym p ; true → sym (snd f)})))
            (Iso.fun (PathIdTruncIso _)
             (isContr→isProp (isConnectedEM (suc (i + zero))) ∣ fst f false ∣ ∣ (0ₖ _) ∣))
    help2 i (suc n) =
      isOfHLevelRetractFromIso 0
        (equivToIso (compEquiv
          (invEquiv (coHom≅coHomRed _ (Ring→AbGroup R) (S₊∙ (suc n)) .fst))
          (fst (Hᵐ⁺ⁿ[Sⁿ,G]≅0 (Ring→AbGroup R) n i))))
        isContrUnit*

  g-cute-equiv : (i n : ℕ) → isEquiv (g-cute n i)
  g-cute-equiv zero n = isEquivBiImpl n zero .fst
    (subst isEquiv (sym pth)
      (snd alt-eq))
    where
    alt-eq : EMR zero ≃ (S₊∙ n →∙ EMR∙ (n +' zero))
    alt-eq = compEquiv (untrunc-HⁿSⁿ-inv R n , isEq-inv R n)
              (isoToEquiv (pre∘∙equiv
              (substEquiv EMR (sym (+'-comm n zero)) , substEMR _)))
    pth : g-comm n zero ≡ alt-eq .fst
    pth = funExt (λ r → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ x → sym (subst⁻Subst EMR (+'-comm n zero)
             (gen-HⁿSⁿ R n .fst x ⌣ₖ r))))
  g-cute-equiv (suc i) n = g-ind-main n i (g-cute-equiv i n)

  g-equiv : (n i : ℕ) → isEquiv (pre-g n i)
  g-equiv n i = subst isEquiv pth (snd help)
    where
    help : EMR i ≃ (S₊∙ n) →∙ EMR∙ (i +' n)
    help = compEquiv (_ , g-cute-equiv i n)
            (isoToEquiv (pre∘∙equiv (substEquiv EMR (sym (+'≡+ i n)) , substEMR (sym (+'≡+ i n)))))

    pth : fst help ≡ pre-g n i
    pth = funExt (λ r → →∙Homogeneous≡ (isHomogeneousEM _)
            (funExt λ y → subst⁻Subst EMR (+'≡+ i n) (r ⌣ₖ gen-HⁿSⁿ R n .fst y)))


module pre-Thom' (B : Pointed ℓ)
         (Q : fst B → Pointed ℓ')
         (conB : isConnected 2 (fst B))
         (R : CommRing ℓ'')
         (n : ℕ)
         (e : Q (snd B) ≃∙ S₊∙ n)
         (c : (b : fst B) → Q b →∙ EM∙ (CommRing→AbGroup R) n)
         (r : c (pt B) ≡ (gen-HⁿSⁿ (CommRing→Ring R) n ∘∙ ≃∙map e)) where
  RR = (CommRing→AbGroup R)
  EMR = EM RR
  EMR∙ = EM∙ RR

  g : (i : ℕ) (b : fst B) → EMR i → Q b →∙ EMR∙ (i +' n)
  fst (g i b x) y = x ⌣ₖ c b .fst y
  snd (g i b x) =
    cong (x ⌣ₖ_) (c b .snd)
    ∙ ⌣ₖ-0ₖ i n x

  isEquiv-g-pt : (i : ℕ) → isEquiv (g i (pt B))
  isEquiv-g-pt i = subst isEquiv (sym help)  (eq .snd)
    where
    eq : EMR i ≃ (Q (pt B) →∙ EMR∙ (i +' n))
    eq = compEquiv (pre-Thom.pre-g R n i , pre-Thom.g-equiv R n i)
                   (isoToEquiv (post∘∙equiv (invEquiv∙ e))) -- 

    help : g i (pt B) ≡ fst eq
    help = funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y → cong (λ y → x ⌣[ R , i , n ]Cₖ y)
               (funExt⁻ (cong fst r) y))

  isEquiv-g : (i : ℕ) (b : fst B) → isEquiv (g i b)
  isEquiv-g i = Iso.inv (elim.isIsoPrecompose
       (λ (x : Unit) → pt B) 1 (λ b → isEquiv (g i b) , isPropIsEquiv _)
       (isConnectedPoint 1 conB (pt B)))
       λ _ → isEquiv-g-pt i

  g-equiv : (i : ℕ) (b : fst B) → EMR i ≃ Q b →∙ EMR∙ (i +' n)
  g-equiv i b = g i b , isEquiv-g i b

  g-pres+ : (i : ℕ) (b : fst B) (x y : EMR i)
             (z : Q b .fst) → g i b (x +ₖ y) .fst z ≡ g i b x .fst z +ₖ g i b y .fst z
  g-pres+ = {!!}

  pre-ϕ : (i : ℕ) → (fst B → EMR i) → (b : fst B) → Q b →∙ EMR∙ (i +' n)
  fst (pre-ϕ i β b) x = β b ⌣ₖ c b .fst x
  snd (pre-ϕ i β b) = cong (β b ⌣ₖ_) (c b .snd)
                    ∙ ⌣ₖ-0ₖ i n (β b)

  pre-ϕIso : (i : ℕ)
    → Iso (fst B → EMR i) ((b : fst B) → Q b →∙ EMR∙ (i +' n))
  Iso.fun (pre-ϕIso i) = pre-ϕ i
  Iso.inv (pre-ϕIso i) r b = invEq (g-equiv i b) (r b)
  Iso.rightInv (pre-ϕIso i) t j b = secEq (g-equiv i b) (t b) j
  Iso.leftInv (pre-ϕIso i) t j b = retEq (g-equiv i b) (t b) j

  invEq-g-pres-+ : (i : ℕ) (b : fst B)
    (x y : Q b →∙ EMR∙ (i +' n)) → invEq (g-equiv i b) x +ₖ invEq (g-equiv i b) y
    ≡ invEq (g-equiv i b)
      ((λ z → fst x z +ₖ fst y z)
      , (cong₂ _+ₖ_ (snd x) (snd y) ∙ rUnitₖ (i +' n) (0ₖ (i +' n))))
  invEq-g-pres-+ = {!!}

  isEq-ϕ : (i : ℕ) → isEquiv (pre-ϕ i)
  isEq-ϕ i = isoToIsEquiv (pre-ϕIso i)

  TotalP : Type _
  TotalP = Σ[ x ∈ fst B ] Q x .fst

  TotalP∙ : Pointed _
  fst TotalP∙ = TotalP
  snd TotalP∙ = pt B , Q (pt B) .snd

  open import Cubical.Data.Nat.Order
  k = ≤-∸-+-cancel

  path : (i : ℕ) → (n ≤ i) → i ≡ (i ∸ n) +' n
  path i p = sym (≤-∸-+-cancel p) ∙ sym (+'≡+ (i ∸ n) n)
  
  cupᵣ : (i : ℕ) → (n ≤ i)
    → coHom i RR TotalP
    → coHom (i ∸ n) RR (fst B)
  cupᵣ i t = ST.map λ f
    → Iso.inv (pre-ϕIso (i ∸ n))
        λ b → (λ s → subst EMR (path i t)
                (f (b , s) -ₖ f (b , pt (Q b))))
             , cong (subst EMR (path i t))
                    (rCancelₖ _ (f (b , snd (Q b))))
             ∙ pre-Thom.substEMR R (path i t)

  gys₁ : (i : ℕ) → (n ≤ i)
    → AbGroupHom (coHomGr i RR TotalP)
                  (coHomGr (i ∸ n) RR (fst B))
  fst (gys₁ i p) = cupᵣ i p
  snd (gys₁ i p) = makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂ (funExt λ b
        → cong (invEq (g-equiv (i ∸ n) b))
            (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ s → {!!}))
          ∙ sym (invEq-g-pres-+ (i ∸ n) b _ _)))

  cup' : (i : ℕ) → (n ≤ i)
       → coHom (i ∸ n) RR (fst B)
       → coHom i RR (fst B)
  cup' i p = ST.map λ f → λ b
    → subst EMR (sym (path i p))
        (pre-ϕ (i ∸ n) f b .fst (pt (Q b)))

  gys₂ : (i : ℕ) → (n ≤ i)
    → AbGroupHom (coHomGr (i ∸ n) RR (fst B))
                  (coHomGr i RR (fst B))
  fst (gys₂ i p) = cup' i p
  snd (gys₂ i p) =
    makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂
        (funExt
         λ x → {!!}))

  gys₃ : (i : ℕ) → (n ≤ i)
       → AbGroupHom (coHomGr i RR (fst B))
                     (coHomGr i RR (TotalP))
  gys₃ i p = coHomHom i fst

  Im₁⊂Ker₂ : (i : ℕ) (t : n ≤ i)
    → (x : _)
    → isInIm (gys₁ i t) x
    → isInKer (gys₂ i t) x
  Im₁⊂Ker₂ i t x =
    PT.rec (squash₂ _ _)
      (uncurry
      (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (squash₂ _ _))
        λ f → J (λ x y → isInKer (gys₂ i t) x)
          (cong ∣_∣₂ (funExt λ b
            → cong (subst EMR (sym (path i t)))
                (cong₂ (λ x y → x ⌣[ R , (i ∸ n) , n ]Cₖ y)
                  refl
                  (c b .snd)
              ∙ ⌣ₖ-0ₖ (i ∸ n) n _)
             ∙ {!!}))))

  Ker₂⊂Im₁ : (i : ℕ) (t : n ≤ i)
    → (x : _)
    → isInKer (gys₂ i t) x
    → isInIm (gys₁ i t) x
  Ker₂⊂Im₁ = {!!}

  cup'' : (i : ℕ) → (n ≤ i)
       → coHom i RR (fst B)
       → coHom i RR (TotalP)
  cup'' i t = coHomFun i fst 
  
  --     subst EMR (sym (path i p))
    --      (pre-ϕ (i ∸ n) f ? .fst ?)
  {- ST.map λ f
    → uncurry λ x y
      → subst EMR (sym (path i p))
          (pre-ϕ (i ∸ n) f x .fst y)
-}
  pst : (i : ℕ) → (n ≤ i)
    → coHom i RR TotalP
    → {!coHom !}
  pst = {!!}

    {-
        λ b
    → (λ s → subst EMR (path i t) (fst f (b , s)))
       , cong (subst EMR (path i t))
           {!fst f ?!}
         ∙ {!!} -}
    {- λ b
    → (λ s → subst EMR (path i t) (fst f (b , s)))
    , cong (subst EMR (path i t))
        {!!}
      ∙ {!!}-} 

module Thom (B : Pointed ℓ)
         (Q : fst B → Pointed ℓ')
         (conB : isConnected 3 (fst B))
         (R : CommRing ℓ'')
         (n : ℕ)
         (e : Q (snd B) ≃∙ S₊∙ n) where
  private
    RR = (CommRing→AbGroup R)
    EMR = EM RR
    EMR∙ = EM∙ RR

  Q*→EM : Q (pt B) →∙ EMR∙ n
  Q*→EM = gen-HⁿSⁿ (CommRing→Ring R) n ∘∙ ≃∙map e

  private
    module hlevcon =
      isConnectedPoint 2 conB
        (λ a → isProp→isSet (isPropIsOfHLevel {A = (Q a →∙ EMR∙ n)} 2))
        (pt B , isOfHLevelRetractFromIso 2
                 (post∘∙equiv e)
                 (hLev-map RR n))

    module con =
      isConnectedPoint 2 conB
       hlevcon.elim ((pt B) , Q*→EM)

  isSetQ→ : (b : fst B) → isSet (Q b →∙ EMR∙ n)
  isSetQ→ = hlevcon.elim

  c : (b : fst B) → Q b →∙ EMR∙ n
  c = con.elim

  c-id : c (pt B) ≡ Q*→EM
  c-id = con.β

  module Thom-inst =
    pre-Thom' B Q (isConnectedSubtr 2 1 conB) R n e c c-id


  g : (i : ℕ) (b : fst B) → EMR i → Q b →∙ EMR∙ (i +' n)
  g = Thom-inst.g

  isEquiv-g : (i : ℕ) (b : fst B) → isEquiv (g i b)
  isEquiv-g i b = Thom-inst.g-equiv i b .snd


  ϕ : (i : ℕ) → (fst B → EMR i) → (b : fst B) → Q b →∙ EMR∙ (i +' n)
  ϕ = Thom-inst.pre-ϕ

  isEquivϕ : (i : ℕ) → isEquiv (ϕ i)
  isEquivϕ = Thom-inst.isEq-ϕ

  ϕIso : (i : ℕ)
    → Iso (fst B → EMR i) ((b : fst B) → Q b →∙ EMR∙ (i +' n))
  ϕIso = Thom-inst.pre-ϕIso

