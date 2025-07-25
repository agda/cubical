{-# OPTIONS --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}

module Cubical.Cohomology.EilenbergMacLane.Gysin where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

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
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open RingStr renaming (_+_ to _+r_)
open PlusBis

private
  variable
    ℓ ℓ' ℓ'' : Level

-- We show that a specific cup product is an
-- equivalence. This will induce the Thom isomorphism.
module ⌣Eq (R' : CommRing ℓ'') where
  R = CommRing→Ring R'
  RR = (CommRing→AbGroup R')
  EMR = EM (CommRing→AbGroup R')
  EMR∙ = EM∙ (CommRing→AbGroup R')

  -- current goal: show that the following map is an equivalence
  pre-g : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (i +' n)
  fst (pre-g n i x) y = x ⌣ₖ gen-HⁿSⁿ-raw R n .fst y
  snd (pre-g n i x) =
    cong (x ⌣ₖ_) (gen-HⁿSⁿ-raw R n .snd)
      ∙ ⌣ₖ-0ₖ i n x


  -- We introduce some alternative versions of the map that
  -- may be easier to work with in some situations.
  g-comm : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (n +' i)
  fst (g-comm n i x) y = gen-HⁿSⁿ-raw R n .fst y ⌣ₖ x
  snd (g-comm n i x) =
      cong (_⌣ₖ x) (gen-HⁿSⁿ-raw R n .snd)
    ∙ 0ₖ-⌣ₖ n i x

  g-cute : (n i : ℕ) → EMR i → S₊∙ n →∙ EMR∙ (i + n)
  g-cute n i x = (subst EMR (+'≡+ i n)
                , subst-EM-0ₖ (+'≡+ i n)) ∘∙ pre-g n i x

  indexIso₁ : (n i : ℕ) → EMR∙ (i + n) ≃∙ EMR∙ (n + i)
  fst (indexIso₁ n i) = substEquiv EMR (+-comm i n)
  snd (indexIso₁ n i) = subst-EM-0ₖ (+-comm i n)

  indexIso₂ : (n i : ℕ) → EMR∙ (n + i) ≃∙ EMR∙ (n +' i)
  fst (indexIso₂ n i) = substEquiv EMR (sym (+'≡+ n i))
  snd (indexIso₂ n i) = subst-EM-0ₖ (sym (+'≡+ n i))

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
    (funExt λ y
      → cong (subst EMR (sym (+'≡+ n i)))
         (cong (subst EMR (+-comm i n))
           ((cong (-ₖ^[ i · n ])
               (cong (subst EMR (+'≡+ i n))
                 (⌣ₖ-comm {G'' = R'} i n x (gen-HⁿSⁿ-raw R n .fst y))))))
      ∙ killTransp EMR -ₖ^[ i · n ] _
         (λ _ x → -ₖ^< i · n >² _ _ _ x) _
         (+'-comm n i)  _ _ _ _ _
         (gen-HⁿSⁿ-raw R n .fst y ⌣ₖ x)))
    where
    killTransp : (A : ℕ → Type ℓ) (-ₖ_ : {n : ℕ} → A n → A n) (a : ℕ)
      → ((n : ℕ) → (x : A n) → -ₖ (-ₖ x) ≡ x)
      → (b : ℕ)
      → (p : a ≡ b) (c : ℕ) (q : b ≡ c) (d : ℕ) (r : c ≡ d) (s : d ≡ a)
      → (base : A a)
      → subst A s (subst A r (-ₖ subst A q (subst A p (-ₖ base)))) ≡ base
    killTransp A f i a = J> (J> (J> λ p b
      → cong (subst A p)
              (transportRefl _ ∙ cong f (transportRefl _ ∙ transportRefl _)
         ∙ a _ b)
      ∙ (λ i → subst A (isSetℕ _ _ p refl i) b)
      ∙ transportRefl b))

  isEquivBiImpl : (n i : ℕ)
    → (isEquiv (g-comm n i) → isEquiv (g-cute n i))
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

  isEquiv-lem : (n i : ℕ)
    → isEquiv (cong {x = 0ₖ (suc i)} {y = 0ₖ (suc i)}
               (g-cute n (suc i)))
    → (x y : EMR (suc i))
    → isEquiv (cong {x = x} {y = y} (g-cute n (suc i)))
  isEquiv-lem n i p =
    EM→Prop (Ring→AbGroup R) i (λ _ → isPropΠ λ _ → isPropIsEquiv _)
      (EM→Prop (Ring→AbGroup R) i (λ _ → isPropIsEquiv _)
        p)

  ΩFunIso : (n i : ℕ) (f : S₊∙ n →∙ EMR∙ (suc (i + n)))
     → Iso (f ≡ f)
            (S₊∙ n →∙ EMR∙ (i + n))
  fst (Iso.fun (ΩFunIso n i f) st) x =
    ΩEM+1→EM-gen (i + n) _ (funExt⁻ (cong fst st) x)
  snd (Iso.fun (ΩFunIso n i f) st) =
      (λ j → ΩEM+1→EM-gen (i + n) (snd f j) λ i → snd (st i) j)
    ∙ ΩEM+1→EM-gen-refl (i + n) _
  Iso.inv (ΩFunIso n i f) st =
    ΣPathP ((funExt (λ x → EM→ΩEM+1-gen _ (fst f x) (fst st x)))
           , flipSquare ((λ j → EM→ΩEM+1-gen (i + n) (snd f j) (snd st j))
                       ▷ (EM→ΩEM+1-gen-0ₖ (i + n) _
                       ∙ EM→ΩEM+1-0ₖ (i + n))))
  Iso.rightInv (ΩFunIso n i f) st =
    →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ x
        → Iso.leftInv (Iso-EM-ΩEM+1-gen (i + n) (fst f x)) (st .fst x))
  Iso.leftInv (ΩFunIso n i f) st =
    →∙HomogeneousSquare (isHomogeneousEM _)
      refl refl (Iso.inv (ΩFunIso n i f)
      (Iso.fun (ΩFunIso n i f) st)) st
      (cong funExt (funExt
        λ x → Iso.rightInv
          (Iso-EM-ΩEM+1-gen (i + n) (fst f x)) λ i → st i .fst x))

  g-cute-ind : (n i : ℕ)
    → g-cute n i
    ≡ Iso.fun (ΩFunIso n i (g-cute n (suc i) (0ₖ (suc i))))
     ∘ cong {x = 0ₖ (suc i)} {y = 0ₖ (suc i)} (g-cute n (suc i))
     ∘ EM→ΩEM+1 i
  g-cute-ind zero zero =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM {G = Ring→AbGroup R} 0)
      (funExt λ y → transportRefl _
        ∙ sym ((λ j → ΩEM+1→EM 0
               (λ i → transportRefl (_⌣ₖ_ {n = 1} {m = 0}
                       (EM→ΩEM+1 0 x i)
                       (gen-HⁿSⁿ-raw R zero .fst y)) j))
             ∙ Iso.leftInv (Iso-EM-ΩEM+1 0)
                (_⌣ₖ_ {n = 0} {m = 0} x (gen-HⁿSⁿ-raw R zero .fst y))))
  g-cute-ind zero (suc i) =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y →
        sym (cong (ΩEM+1→EM (suc i + zero))
        (cong (cong (subst EMR (cong suc (+'≡+ (suc i) zero))))
          (sym (EM→ΩEM+1-distr⌣ₖ0 i x (gen-HⁿSⁿ-raw R zero .fst y))))
    ∙∙ (λ j → transp (λ s → EMR (+'≡+ (suc i) zero (s ∨ ~ j))) (~ j)
                (ΩEM+1→EM (+'≡+ (suc i) zero (~ j))
                  λ k → transp (λ s → EMR (suc (+'≡+ (suc i) zero (s ∧ ~ j))))
                    j
                    (EM→ΩEM+1 (suc i) (_⌣ₖ_ {n = suc i} {m = zero}
                      x (gen-HⁿSⁿ-raw R zero .fst y)) k)))
    ∙∙ cong (subst EMR (λ i₁ → suc (+-zero i (~ i₁))))
        (Iso.leftInv (Iso-EM-ΩEM+1 (suc i)) _)))
  g-cute-ind (suc n) zero = funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y
      → transportRefl _
      ∙ sym (cong (ΩEM+1→EM (suc n))
        ((λ k j → subst EMR (+'≡+ (suc zero) (suc n))
          (sym (EM→ΩEM+1-distr⌣ₖ0n n x
            (gen-HⁿSⁿ-raw R (suc n) .fst y)) k j))
      ∙ (λ j → transp (λ i → Ω (EMR∙ (+'≡+ (suc zero) (suc n) (i ∨ j))) .fst)
                      (~ j)
                λ k → transp (λ i → EMR (+'≡+ (suc zero) (suc n) (i ∨ ~ j)))
                  j (EM→ΩEM+1 (suc n)
                    (x ⌣[ R , 0 , (suc n) ]ₖ gen-HⁿSⁿ-raw R (suc n) .fst y) k))
      ∙ (λ j → subst (λ n → Ω (EMR∙ n) .fst)
                 (isSetℕ (suc (suc n)) (suc (suc n))
                   (+'≡+ (suc zero) (suc n)) refl j)
                  (EM→ΩEM+1 (suc n)
                    (x ⌣[ R , 0 , (suc n) ]ₖ gen-HⁿSⁿ-raw R (suc n) .fst y)))
      ∙ transportRefl _)
     ∙ Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) _))
  g-cute-ind (suc n) (suc i) =
    funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y
      → sym ((cong (ΩEM+1→EM (suc i + suc n)))
               (cong (cong (subst EMR (+'≡+ (suc (suc i)) (suc n))))
                 (sym (EM→ΩEM+1-distr⌣ₖ i n x (gen-HⁿSⁿ-raw R (suc n) .fst y))))
           ∙ (λ j → transp (λ s → EMR (suc (+-suc i n (j ∧ ~ s)))) (~ j)
                  ((ΩEM+1→EM (suc (+-suc i n j))
                    (λ k → transp (λ s → EMR (suc (suc (+-suc i n (~ s ∨ j)))))
                      j (EM→ΩEM+1 (suc (suc (i + n)))
                       (x ⌣ₖ gen-HⁿSⁿ-raw R (suc n) .fst y) k)))))
           ∙ cong (subst EMR (λ i₁ → suc (+-suc i n (~ i₁))))
              (Iso.leftInv (Iso-EM-ΩEM+1 (suc i +' suc n))
                (x ⌣ₖ gen-HⁿSⁿ-raw R (suc n) .fst y))))

  g-ind-main : (n i : ℕ)
    → isEquiv (g-cute n i) → isEquiv (g-cute n (suc i))
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
                              (0ₖ-⌣ₖ (suc i) n (gen-HⁿSⁿ-raw R n .fst x))
                           ∙ subst-EM-0ₖ (+'≡+ (suc i) n)))))
          (Iso.fun PathIdTrunc₀Iso
            (isContr→isProp (help2 i n) ∣ f ∣₂ (0ₕ∙ _))))
    where
    myEq = compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 i)))
             (compEquiv (g-cute n i , eq)
               (isoToEquiv
                (invIso (ΩFunIso n i (g-cute n (suc i) (0ₖ (suc i)))))))

    help : cong (g-cute n (suc i))
         ≡ myEq .fst
    help = funExt
      (λ p → sym
        (Iso.leftInv (ΩFunIso n i (g-cute n (suc i) (0ₖ (suc i)))) _
                        ∙ cong (cong (g-cute n (suc i)))
                           (Iso.rightInv (Iso-EM-ΩEM+1 i) _)))
         ∙ sym (cong
            (λ f → Iso.inv (ΩFunIso n i (g-cute n (suc i) (0ₖ (suc i))))
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
             (isContr→isProp (isConnectedEM (suc (i + zero)))
               ∣ fst f false ∣ ∣ (0ₖ _) ∣))
    help2 i (suc n) =
      isOfHLevelRetractFromIso 0
        (equivToIso (compEquiv
          (invEquiv
            (coHom≅coHomRed _ (Ring→AbGroup R) (S₊∙ (suc n)) .fst))
          (fst (Hᵐ⁺ⁿ[Sⁿ,G]≅0 (Ring→AbGroup R) n i))))
        isContrUnit*

  g-cute-equiv : (i n : ℕ) → isEquiv (g-cute n i)
  g-cute-equiv zero n = isEquivBiImpl n zero .fst
    (subst isEquiv (sym pth)
      (snd alt-eq))
    where
    alt-eq : EMR zero ≃ (S₊∙ n →∙ EMR∙ (n +' zero))
    alt-eq = compEquiv (HⁿSⁿ-raw≃G-inv R n , isEquiv-HⁿSⁿ-raw≃G-inv R n)
              (isoToEquiv (pre∘∙equiv
              (substEquiv EMR (sym (+'-comm n zero)) , subst-EM-0ₖ _)))
    pth : g-comm n zero ≡ alt-eq .fst
    pth = funExt (λ r → →∙Homogeneous≡ (isHomogeneousEM _)
           (funExt λ x → sym (subst⁻Subst EMR (+'-comm n zero)
             (gen-HⁿSⁿ-raw R n .fst x ⌣ₖ r))))
  g-cute-equiv (suc i) n = g-ind-main n i (g-cute-equiv i n)

  -- main lemma
  g-equiv : (n i : ℕ) → isEquiv (pre-g n i)
  g-equiv n i = subst isEquiv pth (snd help)
    where
    help : EMR i ≃ (S₊∙ n) →∙ EMR∙ (i +' n)
    help = compEquiv (_ , g-cute-equiv i n)
            (isoToEquiv
              (pre∘∙equiv
                (substEquiv EMR (sym (+'≡+ i n))
                , subst-EM-0ₖ (sym (+'≡+ i n)))))

    pth : fst help ≡ pre-g n i
    pth = funExt (λ r → →∙Homogeneous≡ (isHomogeneousEM _)
            (funExt λ y
              → subst⁻Subst EMR (+'≡+ i n)
                  (r ⌣ₖ gen-HⁿSⁿ-raw R n .fst y)))

-- We may use the above to construct the (generalised) Thom
-- isomorphism (over a fibration with 0-connected base space)
module preThom
  (B : Pointed ℓ)
  (Q : fst B → Pointed ℓ')
  (conB : isConnected 2 (fst B))
  (R : CommRing ℓ'')
  (n : ℕ)
  (e : Q (snd B) ≃∙ S₊∙ n)
  (c : (b : fst B) → Q b →∙ EM∙ (CommRing→AbGroup R) n)
  (r : c (pt B) ≡ (gen-HⁿSⁿ-raw (CommRing→Ring R) n ∘∙ ≃∙map e))
  where
  RR = (CommRing→AbGroup R)
  EMR = EM RR
  EMR∙ = EM∙ RR

  -- Generalisation of previous map g
  g : (i : ℕ) (b : fst B) → EMR i → Q b →∙ EMR∙ (i +' n)
  fst (g i b x) y = x ⌣ₖ c b .fst y
  snd (g i b x) =
    cong (x ⌣ₖ_) (c b .snd)
    ∙ ⌣ₖ-0ₖ i n x

  isEquiv-g-pt : (i : ℕ) → isEquiv (g i (pt B))
  isEquiv-g-pt i = subst isEquiv (sym help)  (eq .snd)
    where
    eq : EMR i ≃ (Q (pt B) →∙ EMR∙ (i +' n))
    eq = compEquiv (⌣Eq.pre-g R n i , ⌣Eq.g-equiv R n i)
                   (isoToEquiv (post∘∙equiv (invEquiv∙ e))) --

    help : g i (pt B) ≡ fst eq
    help = funExt λ x → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y → cong (λ y → x ⌣[ R , i , n ]Cₖ y)
               (funExt⁻ (cong fst r) y))

  abstract
    isEquiv-g : (i : ℕ) (b : fst B) → isEquiv (g i b)
    isEquiv-g i = Iso.inv (elim.isIsoPrecompose
         (λ (x : Unit) → pt B) 1 (λ b → isEquiv (g i b) , isPropIsEquiv _)
         (isConnectedPoint 1 conB (pt B)))
         λ _ → isEquiv-g-pt i

  g-equiv : (i : ℕ) (b : fst B) → EMR i ≃ Q b →∙ EMR∙ (i +' n)
  g-equiv i b = g i b , isEquiv-g i b

  g⁻ : (i : ℕ) (b : fst B) → Q b →∙ EMR∙ (i +' n) → EMR i
  g⁻ i b = invEq (g-equiv i b)

  private
    g-pres+' : (i : ℕ) (b : fst B) (x y : EMR i) (z : _)
             → g i b (x +ₖ y) .fst z ≡ (g i b x +ₖ∙ g i b y) .fst z
    g-pres+' i b x y z =
      distrR⌣ₖ {G'' = CommRing→Ring R} i n x y (c b .fst z)

  g-pres+ : (i : ℕ) (b : fst B) (x y : EMR i)
             → g i b (x +ₖ y) ≡ g i b x +ₖ∙ g i b y
  g-pres+ i b x y = →∙Homogeneous≡ (isHomogeneousEM (i +' n))
    (funExt (g-pres+' i b x y))

  g⁻-pres+ : (i : ℕ) (b : fst B) (x y : _)
    → g⁻ i b (x +ₖ∙ y) ≡ g⁻ i b x +ₖ g⁻ i b y
  g⁻-pres+ i b =
    morphLemmas.isMorphInv _+ₖ_ _+ₖ∙_
      (g i b)
      (g-pres+ i b)
      (g⁻ i b)
      (secEq (g-equiv i b))
      (retEq (g-equiv i b))

  pre-ϕ : (i : ℕ) → (fst B → EMR i) → (b : fst B) → Q b →∙ EMR∙ (i +' n)
  fst (pre-ϕ i β b) x = β b ⌣ₖ c b .fst x
  snd (pre-ϕ i β b) = cong (β b ⌣ₖ_) (c b .snd)
                    ∙ ⌣ₖ-0ₖ i n (β b)

  -- main results
  pre-ϕIso : (i : ℕ)
    → Iso (fst B → EMR i) ((b : fst B) → Q b →∙ EMR∙ (i +' n))
  Iso.fun (pre-ϕIso i) = pre-ϕ i
  Iso.inv (pre-ϕIso i) r b = invEq (g-equiv i b) (r b)
  Iso.rightInv (pre-ϕIso i) t j b = secEq (g-equiv i b) (t b) j
  Iso.leftInv (pre-ϕIso i) t j b = retEq (g-equiv i b) (t b) j

  pre-ϕ-pres+ : (i : ℕ) → (f g : fst B → EMR i)
    → pre-ϕ i (λ b → f b +ₖ g b) ≡ λ b → pre-ϕ i f b +ₖ∙ pre-ϕ i g b
  pre-ϕ-pres+ i f g = funExt (λ b → →∙Homogeneous≡ (isHomogeneousEM _)
    (funExt (g-pres+' i b (f b) (g b))))

  pre-ϕ⁻-pres+ : (i : ℕ) (f g : (b : fst B) → Q b →∙ EMR∙ (i +' n))
    → Iso.inv (pre-ϕIso i) (λ b → f b +ₖ∙ g b)
    ≡ λ b → (Iso.inv (pre-ϕIso i) f b) +ₖ (Iso.inv (pre-ϕIso i) g b)
  pre-ϕ⁻-pres+ i f g = funExt (λ b → g⁻-pres+ i b (f b) (g b))

  isEq-ϕ : (i : ℕ) → isEquiv (pre-ϕ i)
  isEq-ϕ i = isoToIsEquiv (pre-ϕIso i)

-- The (generalised) Thom isomorphism for a fibration with a simply
-- connected base space.
module genThom (B : Pointed ℓ)
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
  Q*→EM = gen-HⁿSⁿ-raw (CommRing→Ring R) n ∘∙ ≃∙map e

  private
    module hlevcon =
      isConnectedPoint 2 conB
        (λ a → isProp→isSet (
          isPropIsOfHLevel {A = (Q a →∙ EMR∙ n)} 2))
        (pt B , isOfHLevelRetractFromIso 2
                 (post∘∙equiv e)
                 (isSet-Sn→∙EM RR n))

    module con =
      isConnectedPoint 2 conB
       hlevcon.elim ((pt B) , Q*→EM)

  isSetQ→ : (b : fst B) → isSet (Q b →∙ EMR∙ n)
  isSetQ→ = hlevcon.elim

  c : (b : fst B) → Q b →∙ EMR∙ n
  c = con.elim

  c-id : c (pt B) ≡ Q*→EM
  c-id = con.β

  module preThom-inst =
    preThom B Q (isConnectedSubtr 2 1 conB) R n e c c-id

  g : (i : ℕ) (b : fst B) → EMR i → Q b →∙ EMR∙ (i +' n)
  g = preThom-inst.g

  isEquiv-g : (i : ℕ) (b : fst B) → isEquiv (g i b)
  isEquiv-g i b = preThom-inst.g-equiv i b .snd

  ϕ : (i : ℕ) → (fst B → EMR i) → (b : fst B) → Q b →∙ EMR∙ (i +' n)
  ϕ = preThom-inst.pre-ϕ

  isEquivϕ : (i : ℕ) → isEquiv (ϕ i)
  isEquivϕ = preThom-inst.isEq-ϕ

  ϕIso : (i : ℕ)
    → Iso (fst B → EMR i) ((b : fst B) → Q b →∙ EMR∙ (i +' n))
  ϕIso = preThom-inst.pre-ϕIso

-- Now for the 'true' Thom isomphism:
module Thom (B : Pointed ℓ)
         (P : fst B → Type ℓ')
         (P* : P (pt B))
         (conB : isConnected 2 (fst B))
         (R : CommRing ℓ'')
         where
  private
    RR = (CommRing→AbGroup R)
    EMR = EM RR
    EMR∙ = EM∙ RR
    * = snd B

  E = Σ[ x ∈ fst B ] (P x)

  E∙ : Pointed _
  fst E∙ = E
  snd E∙ = * , P*

  πE : E → fst B
  πE = fst

  -- goal: relate cohomology of B to cohomology of
  -- the cofibre of πE:
  EP : Type _
  EP = Pushout (λ _ → tt) πE

  EP∙ : Pointed _
  fst EP∙ = EP
  snd EP∙ = inr (pt B)

  EP-contr : isContr E → Iso EP (fst B)
  Iso.fun (EP-contr c) (inl x) = pt B
  Iso.fun (EP-contr c) (inr x) = x
  Iso.fun (EP-contr c) (push a i) = πE (isContr→isProp c (* , P*) a i)
  Iso.inv (EP-contr c) = inr
  Iso.rightInv (EP-contr c) = λ _ → refl
  Iso.leftInv (EP-contr c) (inl x) = sym (push (* , P*))
  Iso.leftInv (EP-contr c) (inr x) = refl
  Iso.leftInv (EP-contr c) (push a i) j =
    hcomp (λ k → λ {(i = i0) → push (* , P*) (~ j)
                   ; (i = i1) → push a (~ j ∨ k)
                   ; (j = i0) → inr (πE (isContr→isProp c (* , P*) a i))
                   ; (j = i1) → push a (i ∧ k)})
      (push (isContr→isProp c (* , P*) a i) (~ j))

  -- Main goal: establish ((b : fst B) → Q b →∙ EMR∙ k) ≃ (EP∙ →∙ EMR∙ k)
  -- Combined with the previous isos, this gives the Thom isomorphism
  -- Hⁱ(B,R) ≃ Hⁱ⁺ⁿ(EP∙,R)
  Q : fst B → Pointed ℓ'
  Q b = Susp (P b) , north

  F = Σ[ x ∈ fst B ] (Q x .fst)

  B→F : fst B → F
  B→F b = b , north

  FP : Type _
  FP = Pushout (λ _ → tt) B→F

  FP∙ : Pointed _
  fst FP∙ = FP
  snd FP∙ = inr (pt B , north)

  -- step 1: show EP∙ ≃ FP∙, and thus (EP∙ →∙ EMR∙ k) ≃ (FP∙ →∙ EMR∙ k)
  EP→FP : EP → FP
  EP→FP (inl x) = inl x
  EP→FP (inr x) = inr (x , south)
  EP→FP (push (e , p) i) =
    (push e ∙ λ j → inr (e , merid p j)) i

  FP→EP : FP → EP
  FP→EP (inl x) = inl x
  FP→EP (inr (x , north)) = inl tt
  FP→EP (inr (x , south)) = inr x
  FP→EP (inr (x , merid a i)) = push (x , a) i
  FP→EP (push a i) = inl tt

  Iso-EP-FP : Iso EP FP
  Iso.fun Iso-EP-FP = EP→FP
  Iso.inv Iso-EP-FP = FP→EP
  Iso.rightInv Iso-EP-FP (inl x) = refl
  Iso.rightInv Iso-EP-FP (inr (x , north)) = push x
  Iso.rightInv Iso-EP-FP (inr (x , south)) = refl
  Iso.rightInv Iso-EP-FP (inr (x , merid a i)) j =
    compPath-filler' (push x) (λ j₁ → inr (x , merid a j₁)) (~ j) i
  Iso.rightInv Iso-EP-FP (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-EP-FP (inl x) = refl
  Iso.leftInv Iso-EP-FP (inr x) = refl
  Iso.leftInv Iso-EP-FP (push (b , p) i) j =
     (cong-∙ FP→EP (push b) (λ j → inr (b , merid p j))
    ∙ sym (lUnit (push (b , p)))) j i

  EP∙≃FP∙ : EP∙ ≃∙ FP∙
  fst EP∙≃FP∙ = isoToEquiv Iso-EP-FP
  snd EP∙≃FP∙ i = inr (pt B , merid P* (~ i))

  -- step 2: show (FP∙ →∙ A) ≃ ((b : fst B) → Q b →∙ A) for any pointed type A
  -- (taken homogeneous for convenience)
  mapIso : ∀ {ℓ} {A : Pointed ℓ}
    → (isHomogeneous A)
    → Iso ((FP , inr ((pt B) , north)) →∙ A)
           ((b : fst B) → Q b →∙ A)
  fst (Iso.fun (mapIso isHom) r b) y = fst r (inr (b , y))
  snd (Iso.fun (mapIso isHom) r b) =
    cong (fst r) (sym (push b) ∙ push (snd B)) ∙ snd r
  fst (Iso.inv (mapIso {A = A} isHom) r) (inl x) = pt A
  fst (Iso.inv (mapIso isHom) r) (inr (b , p)) = r b .fst p
  fst (Iso.inv (mapIso isHom) r) (push a i) = r a .snd (~ i)
  snd (Iso.inv (mapIso isHom) r) = r (pt B) .snd
  Iso.rightInv (mapIso isHom) r = funExt λ b → →∙Homogeneous≡ isHom refl
  Iso.leftInv (mapIso isHom) r =
    →∙Homogeneous≡ isHom
      (funExt λ { (inl x) → sym (snd r) ∙ cong (fst r) (sym (push (pt B)))
                ; (inr x) → refl
                ; (push a i) j → h a i j})
    where
    h : (a : fst B)
      → Square (sym (snd r) ∙ cong (fst r) (sym (push (pt B))))
               refl
               (sym (cong (fst r)
                 (sym (push a) ∙ push (pt B)) ∙ snd r))
               (cong (r .fst) (push a))
    h a = flipSquare
      ((symDistr (cong (fst r) (sym (push a) ∙ push (pt B)))
                       (snd r)
        ∙∙ cong (sym (snd r) ∙_)
            (cong (cong (fst r)) (symDistr (sym (push a)) (push (pt B)))
            ∙ cong-∙ (fst r) (sym (push (pt B))) (push a))
        ∙∙ assoc (sym (snd r))
                 (cong (fst r) (sym (push (pt B))))
                 (cong (fst r) (push a)))
      ◁ flipSquare
         λ i j → compPath-filler' (sym (snd r)
                         ∙ cong (fst r) (sym (push (pt B))))
                         (cong (fst r) (push a)) (~ j) i)

  -- We get our first iso
  ι : (k : ℕ) → Iso ((b : fst B) → Q b →∙ EMR∙ k) (EP∙ →∙ EMR∙ k)
  ι k =
    compIso (invIso (mapIso (isHomogeneousEM _)))
      (post∘∙equiv (invEquiv∙ EP∙≃FP∙))

  -- we need it to be structure preserving in the obvious way
  ι⁻-pres+ : (k : ℕ) (f g : EP∙ →∙ EMR∙ k)
    → Iso.inv (ι k) (f +ₖ∙ g) ≡
     λ b → (Iso.inv (ι k) f b) +ₖ∙ (Iso.inv (ι k) g b)
  ι⁻-pres+ k f g = funExt λ b
    → →∙Homogeneous≡
      (isHomogeneousEM k)
      (funExt λ { north → refl
                ; south → refl
                ; (merid a i) → refl})

  ι-pres+ : (k : ℕ) (f g : (b : fst B) → Q b →∙ EMR∙ k)
    → Iso.fun (ι k) (λ b → f b +ₖ∙ g b)
     ≡ Iso.fun (ι k) f +ₖ∙ Iso.fun (ι k) g
  ι-pres+ k = morphLemmas.isMorphInv _+ₖ∙_ (λ f g b → f b +ₖ∙ g b)
              (Iso.inv (ι k)) (ι⁻-pres+ k)
              (Iso.fun (ι k))
              (Iso.leftInv (ι k)) (Iso.rightInv (ι k))

  -- We combine it with the generalised thom iso, in order to get the
  -- usual Thom isomorphism

  module _  (n : ℕ) (e : (P (pt B) , P*) ≃∙ S₊∙ n) where
    Q≃ : Q (pt B) ≃∙ S₊∙ (suc n)
    Q≃ = compEquiv∙
          (isoToEquiv
           (congSuspIso
            (equivToIso (fst e))) , refl)
            (isoToEquiv (invIso (IsoSucSphereSusp n))
              , IsoSucSphereSusp∙ n)

    module con (c : (b : fst B) → Q b →∙ EM∙ (CommRing→AbGroup R) (suc n))
           (r : c (pt B) ≡ (gen-HⁿSⁿ-raw (CommRing→Ring R) (suc n) ∘∙ ≃∙map Q≃))
           where
      module M = preThom B Q conB R (suc n) Q≃ c r

      -- Finally, the actual Thom ismorphism
      ϕ-raw : (i : ℕ) → (fst B → EMR i) ≃ (EP∙ →∙ EMR∙ (i +' suc n))
      ϕ-raw i = isoToEquiv (compIso (M.pre-ϕIso i) (ι (i +' (suc n))))

      ϕ-equiv : (i : ℕ) → coHom i RR (fst B) ≃ coHomRed (i +' suc n) RR EP∙
      ϕ-equiv i =
        isoToEquiv (setTruncIso (compIso (M.pre-ϕIso i) (ι (i +' (suc n)))))

      ϕ-raw-contr : (i : ℕ) → isContr E → (fst B → EMR i) ≃ (B →∙ EMR∙ (i +' suc n))
      ϕ-raw-contr i contr =
        compEquiv (ϕ-raw i)
          (isoToEquiv (post∘∙equiv (isoToEquiv (EP-contr contr) , refl)))

      ϕ : (i : ℕ) → coHom i RR (fst B) → coHomRed (i +' suc n) RR EP∙
      ϕ i = ϕ-equiv i .fst

      isHomϕ : (i : ℕ)
        → (x y : coHom i RR (fst B)) → ϕ i (x +ₕ y) ≡ ϕ i x +ₕ∙ ϕ i y
      isHomϕ i =
        ST.elim2 (λ _ _ → isSetPathImplicit)
          λ f g → cong ∣_∣₂ (cong (Iso.fun (ι (i +' suc n)))
                             (M.pre-ϕ-pres+ i f g)
                          ∙ ι-pres+ (i +' suc n)
                             (λ b → M.g i b (f b)) (λ b → M.g i b (g b))
                          ∙ →∙Homogeneous≡ (isHomogeneousEM (i +' suc n)) refl)

      ϕHom : (i : ℕ) → AbGroupHom (coHomGr i RR (fst B))
                                    (coHomRedGr (i +' suc n) RR EP∙)
      fst (ϕHom i) = ϕ i
      snd (ϕHom i) = makeIsGroupHom (isHomϕ i)

      ϕGrEquiv : (i : ℕ) → AbGroupEquiv (coHomGr i RR (fst B))
                                          (coHomRedGr (i +' suc n) RR EP∙)
      fst (ϕGrEquiv i) = ϕ-equiv i
      snd (ϕGrEquiv i) = ϕHom i .snd

  -- For the Gysin sequence, we will be need the long exact sequence
  -- in cohomology related to the cofibre EP∙, i.e.
  -- ... → Hⁱ⁻¹(E,R) → H̃ⁱ(EP∙,R) → Hⁱ(B,R) → Hⁱ(E,R) → ...
  pre-E↑ : (i : ℕ) → (E → EM RR i) → EP∙ →∙ EM∙ RR (suc i)
  fst (pre-E↑ i f) (inl x) = 0ₖ (suc i)
  fst (pre-E↑ i f) (inr x) = 0ₖ (suc i)
  fst (pre-E↑ i f) (push a i₁) = EM→ΩEM+1 i (f a) i₁
  snd (pre-E↑ i f) = refl

  E↑ : (i : ℕ) → AbGroupHom (coHomGr i RR E) (coHomRedGr (suc i) RR EP∙)
  fst (E↑ i) = ST.map (pre-E↑ i)
  snd (E↑ i) =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isSetPathImplicit)
        λ f g → cong ∣_∣₂
          (→∙Homogeneous≡ (isHomogeneousEM (suc i))
           (funExt λ { (inl x) → sym (rUnitₖ (suc i) (0ₖ (suc i)))
                     ; (inr x) → sym (rUnitₖ (suc i) (0ₖ (suc i)))
                     ; (push a j) → flipSquare (help i (f a) (g a)) j})))
    where
    help : (i : ℕ) (x y : EM RR i)
      → PathP (λ j → rUnitₖ {G = RR} (suc i) (0ₖ (suc i)) (~ j)
                   ≡ rUnitₖ (suc i) (0ₖ (suc i)) (~ j))
               (EM→ΩEM+1 {G = RR} i (x +ₖ y))
               (cong₂ _+ₖ_ (EM→ΩEM+1 i x) (EM→ΩEM+1 i y))
    help zero x y = EM→ΩEM+1-hom zero x y
                  ∙ sym (cong₂+₁ (EM→ΩEM+1 zero x) (EM→ΩEM+1 zero y))
    help (suc n) x y = EM→ΩEM+1-hom (suc n) x y
                  ∙ sym (cong₂+₂ n (EM→ΩEM+1 (suc n) x)
                                 (EM→ΩEM+1 (suc n) y))

  j* : (i : ℕ) → AbGroupHom (coHomRedGr i RR EP∙) (coHomGr i RR (fst B))
  fst (j* i) = ST.map λ f b → fst f (inr b)
  snd (j* i) = makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit) λ f g → refl)

  p* : (i : ℕ) → AbGroupHom (coHomGr i RR (fst B)) (coHomGr i RR E)
  p* i = coHomHom i fst

  Im-j*⊂Ker-p* : (i : ℕ) (x : _)
    → isInIm (j* i) x
    → isInKer (p* i) x
  Im-j*⊂Ker-p* i =
    ST.elim
      (λ f → isSetΠ λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
        (uncurry (ST.elim (λ _ → isSetΠ
          λ _ → isSetPathImplicit)
          λ g p → PT.rec (squash₂ _ _)
            (J (λ f _ → isInKer (p* i) ∣ f ∣₂)
              (cong ∣_∣₂ (funExt (λ a
              → cong (fst g) (sym (push a) ∙ push (pt B , P*))
              ∙ snd g))))
            (Iso.fun PathIdTrunc₀Iso p)))

  Ker-p*⊂Im-j* : (i : ℕ) (x : _)
    → isInKer (p* i) x
    → isInIm (j* i) x
  Ker-p*⊂Im-j* i =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
     λ f p → PT.map
       (λ p → ∣ (λ { (inl x) → 0ₖ i
                   ; (inr x) → f x
                   ; (push a i) → p (~ i) a})
             , funExt⁻ p (pt B , P*) ∣₂
             , refl)
       (Iso.fun PathIdTrunc₀Iso p)

  Im-p*⊂Ker-E↑ : (i : ℕ) (x : _)
    → isInIm (p* i) x
    → isInKer (E↑ i) x
  Im-p*⊂Ker-E↑ i = ST.elim
      (λ f → isSetΠ λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
         (uncurry (ST.elim (λ _ → isSetΠ
          λ _ → isSetPathImplicit)
          λ g p → PT.rec (squash₂ _ _)
            (J (λ f _ → isInKer (E↑ i) ∣ f ∣₂)
              (cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM _)
                (funExt λ { (inl x) → refl
                          ; (inr x) → sym (EM→ΩEM+1 i (g x))
                          ; (push a j) k
                            → EM→ΩEM+1 i (g (fst a)) (j ∧ ~ k)}))))
            (Iso.fun PathIdTrunc₀Iso p)))

  Ker-E↑⊂Im-p* : (i : ℕ) (x : _)
    → isInKer (E↑ i) x
    → isInIm (p* i) x
  Ker-E↑⊂Im-p* i =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
      λ f p → PT.map (λ r →
        ∣ (λ b → ΩEM+1→EM i (sym (funExt⁻ (cong fst r) (inr b)))
                             +ₖ f (* , P*)) ∣₂
      , cong ∣_∣₂ (funExt λ {(x , p)
        → cong (_+ₖ f (* , P*))
             ((cong (ΩEM+1→EM i)
            (cong sym (sym (fromPathP (cong (funExt⁻ (cong fst r)) (push (x , p))))
                    ∙ (λ j → transp (λ k → EM→ΩEM+1 i (f (x , p)) (j ∨ k)
                                           ≡ 0ₖ (suc i))
                         j (compPath-filler'
                            (sym (EM→ΩEM+1 i (f (x , p))))
                            (funExt⁻ (cong fst r) (inl tt)) j)))
            ∙ (symDistr (sym (EM→ΩEM+1 i (f (x , p))))
                        (funExt⁻ (λ i₂ → fst (r i₂)) (inl tt))))
          ∙ ΩEM+1→EM-hom i
              (sym (funExt⁻ (λ i₁ → fst (r i₁)) (inl tt)))
              (EM→ΩEM+1 i (f (x , p))))
            ∙ cong₂ _+ₖ_
               (cong (ΩEM+1→EM i)
                 (cong sym
                   (rUnit _ ∙∙ sym (Square→compPath
                   ((cong (funExt⁻ (cong fst r)) (push (* , P*)))
                 ▷ λ i j → r j .snd i)) ∙∙ sym (rUnit _))))
               (Iso.leftInv (Iso-EM-ΩEM+1 i) (f (x , p))))
         ∙ cong₂ _+ₖ_ (cong₂ _+ₖ_ (cong (ΩEM+1→EM i)
                       (sym (EM→ΩEM+1-sym i (f (* , P*))))
                      ∙ Iso.leftInv (Iso-EM-ΩEM+1 i) (-ₖ (f (* , P*)))) refl
                    ∙ commₖ i (-ₖ f (* , P*)) (f (x , p)))
                    refl
         ∙ sym (assocₖ i (f (x , p)) (-ₖ (f (* , P*))) (f (* , P*)))
         ∙ cong₂ _+ₖ_ refl (lCancelₖ i (f (* , P*)))
         ∙ rUnitₖ i (f (x , p))}))
        ((Iso.fun PathIdTrunc₀Iso p))

  Im-E↑⊂Ker-j* : (i : ℕ) (x : _)
    → isInIm (E↑ i) x
    → isInKer (j* (suc i)) x
  Im-E↑⊂Ker-j* i = ST.elim
      (λ f → isSetΠ λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
         (uncurry (ST.elim (λ _ → isSetΠ
          λ _ → isSetPathImplicit)
          λ g p → PT.rec (squash₂ _ _)
            (J (λ f _ → isInKer (j* (suc i)) ∣ f ∣₂) refl)
            (Iso.fun PathIdTrunc₀Iso p)))

  Ker-j*⊂Im-E↑ : (i : ℕ) (x : _)
    → isInKer (j* (suc i)) x
    → isInIm (E↑ i) x
  Ker-j*⊂Im-E↑ i =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
      λ f p → PT.map
       (λ p → ∣ (λ b → ΩEM+1→EM i (pth b f (funExt⁻ p))) ∣₂
            , cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt λ { (inl x) → sym (snd f)
                                   ∙ cong (fst f) (sym (push (* , P*)))
                        ; (inr x) → sym (funExt⁻ p x)
                        ; (push a j) → main a f (funExt⁻ p) j})))
       (Iso.fun PathIdTrunc₀Iso p)
    where
    pth : (a : E) (f : EP∙ →∙ EM∙ RR (suc i))
       (p : (b : fst B) → fst f (inr b) ≡ 0ₖ (suc i))
     → fst (Ω (EMR∙ (suc i)))
    pth a f p = sym (snd f) ∙ cong (fst f) (sym (push (* , P*)))
             ∙∙ cong (fst f) (push a)
             ∙∙ p (fst a)

    main : (a : E) (f : EP∙ →∙ EM∙ RR (suc i))
       (p : (b : fst B) → fst f (inr b) ≡ 0ₖ (suc i))
       →  PathP (λ j → EM→ΩEM+1 i (ΩEM+1→EM i (pth a f p)) j
                 ≡ f .fst (push a j))
            (sym (snd f) ∙ cong (fst f) (sym (push (* , P*))))
            (sym (p (fst a)))
    main a f p =
      flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 i) (pth a f p)
               ◁ λ j i → doubleCompPath-filler
                    (sym (snd f) ∙ cong (fst f) (sym (push (* , P*))))
                    (cong (fst f) (push a))
                    (p (fst a)) (~ j) i)

module Gysin (B : Pointed ℓ)
         (P : fst B → Type ℓ')
         (conB : isConnected 2 (fst B))
         (R : CommRing ℓ'')
         (n : ℕ)
         (eq' : P (pt B) ≃ S₊ n)
         (c : (b : fst B) → Susp∙ (P b) →∙ EM∙ (CommRing→AbGroup R) (suc n))
         (c-id : c (pt B) ≡ gen-HⁿSⁿ-raw
           (CommRing→Ring R) (suc n)
           ∘∙ ≃∙map (Thom.Q≃ B P (invEq eq' (ptSn n))
              conB R n (eq' , (secEq eq' (ptSn n)))))
         where
  private
     RR = (CommRing→AbGroup R)
     EMR = EM RR
     EMR∙ = EM∙ RR
     P* = invEq eq' (ptSn n)
  module M = Thom B P P* conB R
  open M public

  eq : (P (pt B) , P*) ≃∙ S₊∙ n
  fst eq = eq'
  snd eq = secEq eq' (ptSn n)

  module _ (c-id : c (pt B) ≡ gen-HⁿSⁿ-raw (CommRing→Ring R) (suc n) ∘∙ ≃∙map (Q≃ n eq)) where
    module L = con n eq c c-id
    open L

    -- The Euler class
    e : coHom (suc n) RR (fst B)
    e = ∣ (λ b → c b .fst south) ∣₂

    minusPath : (i : ℕ) → (suc n ≤ i) → (i ∸ suc n) +' suc n ≡ i
    minusPath i p = +'≡+ (i ∸ suc n) (suc n) ∙ ≤-∸-+-cancel p

    -- The main map in the sequence
    ⌣-hom : (i : ℕ) → (suc n ≤ i)
      → AbGroupHom (coHomGr (i ∸ suc n) RR (fst B))
                    (coHomGr i RR (fst B))
    fst (⌣-hom i t) f =
      subst (λ i → coHom i RR (fst B)) (minusPath i t) (f ⌣ e)
    snd (⌣-hom i t) =
      makeIsGroupHom
          (λ f g → cong (subst (λ i₁ → coHom i₁ RR (fst B)) (minusPath i t))
                      (distrR⌣ (i ∸ suc n) (suc n) f g e)
                  ∙ IsGroupHom.pres· (snd (substℕ-coHom (minusPath i t)))
                      (f ⌣ e) (g ⌣ e))

    private
      helpIso : (i : ℕ) → suc n ≤ i
        → AbGroupEquiv (coHomRedGr i RR EP∙)
            (coHomGr (i ∸ suc n) RR (fst B))
      helpIso i t =
        compGroupEquiv (substℕ-coHomRed (sym (minusPath i t)))
            (invGroupEquiv (ϕGrEquiv (i ∸ suc n)))

      alt-hom : (i : ℕ) → (suc n ≤ i)
        → AbGroupHom (coHomGr (i ∸ suc n) RR (fst B))
                      (coHomGr i RR (fst B))
      alt-hom i t =
        compGroupHom (ϕHom (i ∸ suc n))
          (compGroupHom (j* _)
          (GroupEquiv→GroupHom (substℕ-coHom (minusPath i t))))

      ⌣≡alt : (i : ℕ) (t : suc n ≤ i)
        → ⌣-hom i t ≡ alt-hom i t
      ⌣≡alt i t = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (ST.elim (λ _ → isSetPathImplicit) λ _ → refl))


    -- the other two maps
    mapₗ : (i : ℕ) → suc n ≤ suc i
        → AbGroupHom (coHomGr i RR E)
                      (coHomGr (suc i ∸ suc n) RR (fst B))
    mapₗ i t =
      compGroupHom (E↑ i)
         (GroupEquiv→GroupHom
           (helpIso (suc i) t))

    mapᵣ : (i : ℕ)
        → AbGroupHom (coHomGr i RR (fst B))
                      (coHomGr i RR E)
    mapᵣ i = p* i


    -- Finally: exactness
    Im-mapᵣ⊂Ker-mapₗ : (i : ℕ) (t : suc n ≤ suc i) (x : coHom i RR E)
      → isInIm (mapᵣ i) x
      → isInKer (mapₗ i t) x
    Im-mapᵣ⊂Ker-mapₗ i t x s =
        cong (invEq (fst (ϕGrEquiv (suc i ∸ suc n))))
          (cong (subst (λ i → coHomRed i RR EP∙) (sym (minusPath (suc i) t)))
            (M.Im-p*⊂Ker-E↑ i x s))
      ∙ IsGroupHom.pres1 (helpIso (suc i) t .snd)

    Ker-mapₗ⊂Im-mapᵣ : (i : ℕ) (t : suc n ≤ suc i) (x : coHom i RR E)
      → isInKer (mapₗ i t) x
      → isInIm (mapᵣ i) x
    Ker-mapₗ⊂Im-mapᵣ i t x p =
      Ker-E↑⊂Im-p* i x
        (sym (retEq (fst (helpIso (suc i) t)) (E↑ i .fst x))
        ∙ cong (invEq (fst (helpIso (suc i) t))) p
        ∙ IsGroupHom.pres1 (invGroupEquiv (helpIso (suc i) t) .snd))

    private
      j*≡ : (i : ℕ) (t : suc n ≤  i)
         → (x : _) → j* i .fst x
                     ≡ fst (alt-hom i t)
                        (fst (helpIso i t) .fst x)
      j*≡ i t f = cong (j* i .fst)
               (sym (substSubst⁻ (λ i → coHomRed i RR EP∙) (minusPath i t) f))
            ∙  sym (substCommSlice (λ i → coHomRed i RR EP∙)
                 (λ i → coHom i RR (fst B)) (λ i → j* i .fst) (minusPath i t)
                 (subst (λ i → coHomRed i RR EP∙) (sym (minusPath i t)) f))
            ∙ cong (subst (λ i → coHom i RR (fst B)) (minusPath i t))
                (cong (j* ((i ∸ suc n) +' (suc n)) .fst)
                  (sym (secEq (ϕGrEquiv (i ∸ suc n) .fst)
                    (subst (λ i → coHomRed i RR EP∙) (sym (minusPath i t))
                      f))))

    Ker-⌣⊂Im-mapₗ : (i : ℕ) (t : suc n ≤  suc i)
      (x : coHom (suc i ∸ suc n) RR (fst B))
      → isInKer (⌣-hom (suc i) t) x
      → isInIm (mapₗ i t) x
    Ker-⌣⊂Im-mapₗ i t x s =
      →Im (Ker-j*⊂Im-E↑ i _
          ((j*≡ (suc i) t _
          ∙ cong (fst (alt-hom (suc i) t))
            (secEq (fst (helpIso (suc i) t)) x))
        ∙ funExt⁻ (cong fst (sym (⌣≡alt (suc i) t))) x ∙ s))
      where
      →Im : isInIm (E↑ i) (invEq (fst (helpIso (suc i) t)) x)
        → isInIm (mapₗ i t) x
      →Im = PT.map (uncurry λ f p → f
                   , cong (fst (fst (helpIso (suc i) t))) p
                   ∙ secEq (fst (helpIso (suc i) t)) _)


    Im-mapₗ⊂Ker-⌣ : (i : ℕ) (t : suc n ≤  suc i)
        (x : coHom (suc i ∸ suc n) RR (fst B))
        → isInIm (mapₗ i t) x
        → isInKer (⌣-hom (suc i) t) x
    Im-mapₗ⊂Ker-⌣ i t x p =
        (((λ j → ⌣≡alt (suc i) t j .fst x)
      ∙ cong (fst (alt-hom (suc i) t))
         (sym (secEq (fst (helpIso (suc i) t)) x)))
      ∙ sym (j*≡ (suc i) t (invEq (helpIso (suc i) t .fst) x)))
      ∙ Im-E↑⊂Ker-j* i _ (Im-transf x p)
      where
      Im-transf : (x : _) → isInIm (mapₗ i t) x
        → isInIm (E↑ i) (invEq (helpIso (suc i) t .fst) x)
      Im-transf f = PT.map (uncurry λ g p → g
        , sym (retEq (helpIso (suc i) t .fst) (E↑ i .fst g))
        ∙ cong (invEq (helpIso (suc i) t .fst)) p)

    Im--⌣⊂Ker-mapᵣ : (i : ℕ) (t : suc n ≤ i) (x : coHom i RR (fst B))
      → isInIm (⌣-hom i t) x
      → isInKer (mapᵣ i) x
    Im--⌣⊂Ker-mapᵣ i t x p =
      Im-j*⊂Ker-p* i x
        (PT.map
          (uncurry (λ f p → invEq (helpIso i t .fst) f
          , ((j*≡ i t (invEq (helpIso i t .fst) f)
          ∙ cong (alt-hom i t .fst)
             (secEq (fst (helpIso i t)) f))
          ∙ ((λ j → ⌣≡alt i t (~ j) .fst f)))
           ∙ refl
          ∙ p)) p)


    Ker-mapᵣ⊂Im--⌣ : (i : ℕ) (t : suc n ≤ i) (x : coHom i RR (fst B))
      → isInKer (mapᵣ i) x
      → isInIm (⌣-hom i t) x
    Ker-mapᵣ⊂Im--⌣ i t x p =
      subst (λ f → isInIm f x) (sym (⌣≡alt i t))
        (→Im x (Ker-p*⊂Im-j* i x p))
      where
      →Im : (x : _) → isInIm (j* i) x → isInIm (alt-hom i t) x
      →Im x = PT.map (uncurry λ f p → (fst (helpIso i t .fst) f)
        , sym (j*≡ i t f)
         ∙ p)



module GysinCon (B : Pointed ℓ)
         (P : fst B → Type ℓ')
         (conB : isConnected 3 (fst B))
         (R : CommRing ℓ'')
         (n : ℕ)
         (eq : P (pt B) ≃ S₊ n)
         where
  private
    module T = Thom B P (invEq eq (ptSn n)) (isConnectedSubtr 2 1 conB) R
    module GT = genThom B
      (λ b → Susp∙ (P b)) conB R (suc n) (T.Q≃ n (eq , secEq eq (ptSn n)))

  module Inst = Gysin B P (isConnectedSubtr 2 1 conB)
                      R
                      n
                      eq
                      GT.c
                      GT.c-id

  open Inst public
