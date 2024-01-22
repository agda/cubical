{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RPinf where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin

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
open import Cubical.Homotopy.EilenbergMacLane.Order2

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
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.RPn

open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary


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
open import Cubical.Algebra.CommRing hiding (_ˣ)
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin.Base



open RingStr renaming (_+_ to _+r_)
open PlusBis

open Iso

-- move to Bool?
Bool→Bool→∙Bool : Bool → (Bool , true) →∙ (Bool , true)
Bool→Bool→∙Bool false = idfun∙ _
Bool→Bool→∙Bool true = const∙ _ _

Iso-Bool→∙Bool-Bool : Iso ((Bool , true) →∙ (Bool , true)) Bool
Iso.fun Iso-Bool→∙Bool-Bool f = fst f false
Iso.inv Iso-Bool→∙Bool-Bool = Bool→Bool→∙Bool
Iso.rightInv Iso-Bool→∙Bool-Bool false = refl
Iso.rightInv Iso-Bool→∙Bool-Bool true = refl
Iso.leftInv Iso-Bool→∙Bool-Bool f = Σ≡Prop (λ _ → isSetBool _ _) (help _ refl)
  where
  help : (x : Bool) → fst f false ≡ x
    → Bool→Bool→∙Bool (fst f false) .fst ≡ f .fst
  help false p = funExt
    λ { false → (λ j → Bool→Bool→∙Bool (p j) .fst false) ∙ sym p
      ; true → (λ j → Bool→Bool→∙Bool (p j) .fst true) ∙ sym (snd f)}
  help true p = (λ j → Bool→Bool→∙Bool (p j) .fst)
              ∙ funExt λ { false → sym p ; true → sym (snd f)}

-- pres0→hom
pres0→GroupIso : ∀ {ℓ} {G : Group ℓ} (f : fst G ≃ ℤ/2 .fst)
  → fst f (GroupStr.1g (snd G)) ≡ fzero
  → IsGroupHom (snd G) (fst f) ((ℤGroup/ 2) .snd)
pres0→GroupIso {G = G} f fp = isGroupHomInv ((invEquiv f) , main)
  where
  one = invEq f fone

  f⁻∙ : invEq f fzero ≡ GroupStr.1g (snd G)
  f⁻∙ = sym (cong (invEq f) fp) ∙ retEq f _

  f⁻1 : GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)
      ≡ GroupStr.1g (snd G)
  f⁻1 = sym (retEq f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)))
    ∙∙ cong (invEq f) (mainlem _ refl ∙ sym fp)
    ∙∙ retEq f (GroupStr.1g (snd G))
    where
    l : ¬ (fst f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone))
                ≡ fone)
    l p = snotz (cong fst q)
      where
      q : fone ≡ fzero
      q = (sym (secEq f fone)
        ∙ cong (fst f)
            ((sym (GroupStr.·IdL (snd G) one)
            ∙ cong (λ x → GroupStr._·_ (snd G) x one) (sym (GroupStr.·InvL (snd G) one)))
            ∙ sym (GroupStr.·Assoc (snd G) (GroupStr.inv (snd G) one) one one)))
        ∙ cong (fst f) (cong (GroupStr._·_ (snd G) (GroupStr.inv (snd G) (invEq f fone)))
                ((sym (retEq f _) ∙ cong (invEq f) p)))
        ∙ cong (fst f) (GroupStr.·InvL (snd G) _)
        ∙ fp


    mainlem : (x : _)
      → fst f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)) ≡ x
      → f .fst ((snd G GroupStr.· invEq f fone) (invEq f fone)) ≡ fzero
    mainlem = ℤ/2-elim
      (λ p → p)
      λ p → ⊥.rec (l p)


  main : IsGroupHom ((ℤGroup/ 2) .snd) (invEq f) (snd G)
  main =
    makeIsGroupHom
      (ℤ/2-elim
        (ℤ/2-elim (f⁻∙ ∙ sym (GroupStr.·IdR (snd G) (GroupStr.1g (snd G)))
                       ∙ cong (λ x → snd G .GroupStr._·_ x x) (sym f⁻∙))
                  (sym (GroupStr.·IdL (snd G) one)
                  ∙ cong (λ x → snd G .GroupStr._·_ x one) (sym f⁻∙)))
        (ℤ/2-elim (sym (GroupStr.·IdR (snd G) one)
                  ∙ cong (snd G .GroupStr._·_ (invEq f fone)) (sym f⁻∙))
                  (f⁻∙ ∙ sym f⁻1)))

-----------------------------------------------------------

-- move to Cohomology GroupStr or somethign
EM→-charac : ∀ {ℓ ℓ'} {A : Pointed ℓ} {G : AbGroup ℓ'} (n : ℕ)
  → Iso (fst A → EM G n) ((A →∙ EM∙ G n) × EM G n)
Iso.fun (EM→-charac {A = A} n) f =
  ((λ x → f x -ₖ f (pt A)) , rCancelₖ n (f (pt A))) , f (pt A)
Iso.inv (EM→-charac n) (f , a) x = fst f x +ₖ a
Iso.rightInv (EM→-charac {A = A} n) ((f , p) , a) =
  ΣPathP (→∙Homogeneous≡ (isHomogeneousEM _)
    (funExt (λ x → (λ i → (f x +ₖ a) -ₖ (cong (_+ₖ a) p ∙ lUnitₖ n a) i)
                  ∙ sym (assocₖ n (f x) a (-ₖ a))
                  ∙ cong (f x +ₖ_) (rCancelₖ n a)
                  ∙ rUnitₖ n (f x)))
  , cong (_+ₖ a) p ∙ lUnitₖ n a)
Iso.leftInv (EM→-charac {A = A} n) f =
  funExt λ x → sym (assocₖ n (f x) (-ₖ f (pt A)) (f (pt A)))
    ∙∙ cong (f x +ₖ_) (lCancelₖ n (f (pt A)))
    ∙∙ rUnitₖ n (f x)

0ˣ : ∀ {ℓ} (A : ℕ → Type ℓ) (0A : (n : ℕ) → A n) → (n : ℕ) → A ˣ n 
0ˣ A 0A zero = 0A zero
0ˣ A 0A (suc n) = (0ˣ A 0A n) , (0A (suc n))

EM-ℤ/2ˣ∙ : (n : ℕ) → EM ℤ/2 ˣ n
EM-ℤ/2ˣ∙ = 0ˣ (EM ℤ/2) 0ₖ

private
  nonConst→∙ : (b : EM ℤ/2 1) → Type _
  nonConst→∙ b =
    Σ[ F ∈ Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1 ]
      (¬ F ≡ const∙ _ _)

  Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool :
    Iso (Susp∙ (Ω (EM∙ ℤ/2 1) .fst)
         →∙ EM∙ ℤ/2 1)
        ((Bool , true) →∙ (Bool , true))
  Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool = compIso
    (invIso (ΩSuspAdjointIso {A = Ω (EM∙ ℤ/2 1)}))
    (compIso (post∘∙equiv (lem , refl)) (pre∘∙equiv (lem , refl)))
    where
    lem = isoToEquiv
      (compIso (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 0))
               (invIso (Bool≅ℤGroup/2 .fst)))

  Σ¬Iso : ∀ {ℓ} {B A : Type ℓ}
    → (e : A ≃ B)
    → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)
  Σ¬Iso {B = B} =
    EquivJ (λ A e → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)) idIso

  nonConst→∙Iso : Iso (nonConst→∙ embase) (Σ[ F ∈ Bool ] ¬ F ≡ true)
  nonConst→∙Iso =
    Σ¬Iso (isoToEquiv
           (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool
                    Iso-Bool→∙Bool-Bool))

  isProp-nonConst→∙ : (b : EM ℤ/2 1) → isProp (nonConst→∙ b)
  isProp-nonConst→∙ = EM→Prop _ 0 (λ _ → isPropIsProp)
           (isOfHLevelRetractFromIso 1 nonConst→∙Iso
             (isContr→isProp ((false , true≢false ∘ sym)
                         , λ { (false , p) → Σ≡Prop (λ _ → isProp¬ _) refl
                             ; (true , p) → ⊥.rec (p refl)})))

eRP∞∙ : Susp∙ (Ω (EM∙ ℤ/2 1) .fst) →∙ EM∙ ℤ/2 1
fst eRP∞∙ north = embase
fst eRP∞∙ south = embase
fst eRP∞∙ (merid a i) = a i
snd eRP∞∙ = refl

eRP∞-nonConst : nonConst→∙ embase
fst eRP∞-nonConst = eRP∞∙
snd eRP∞-nonConst p = true≢false true≡false
  where
  true≡false : true ≡ false
  true≡false i =
    Iso.fun (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool Iso-Bool→∙Bool-Bool)
      (p (~ i))

eRP∞ : (b : EM ℤ/2 1) → nonConst→∙ b
eRP∞ = EM→Prop ℤ/2 0 isProp-nonConst→∙ eRP∞-nonConst

module ThomRP∞ = Thom (EM∙ ℤ/2 1) (0ₖ 1 ≡_) refl
                      (isConnectedEM 1)
                      ℤ/2CommRing

open ThomRP∞
isContrE : isContr E
isContrE = isContrSingl _

module conRP∞ =
  con 0 (((compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 0)))
                   (isoToEquiv (invIso (fst Bool≅ℤGroup/2))))) , refl)
        (λ b → eRP∞ b .fst)
        (Iso.inv (congIso (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool
                                   Iso-Bool→∙Bool-Bool)) λ i → false)

open conRP∞
ϕ-raw-contrRP∞ : (n : ℕ)
  → ((EM ℤ/2 1 → EM ℤ/2 n))
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1))
ϕ-raw-contrRP∞ n = ϕ-raw-contr n isContrE

⌣RP∞ : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
  → EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1)
fst (⌣RP∞ n f) x = (f x) ⌣[ ℤ/2Ring R]ₖ x
snd (⌣RP∞ n f) = ⌣ₖ-0ₖ _ _ (f (0ₖ 1))

⌣RP∞' : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
  → EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (1 +' n)
fst (⌣RP∞' n f) x = x ⌣[ ℤ/2Ring R]ₖ (f x)
snd (⌣RP∞' n f) = 0ₖ-⌣ₖ _ _ (f (0ₖ 1))

⌣RP∞≡⌣RP∞' : (n : ℕ) →
  PathP (λ i →
   (EM ℤ/2 1 → EM ℤ/2 n) →
    EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (+'-comm n 1 i))
  (⌣RP∞ n)
  (⌣RP∞' n)
⌣RP∞≡⌣RP∞' n = funExt λ f →
  →∙HomogeneousPathP refl (cong (EM∙ ℤ/2) (+'-comm n 1))
    (isHomogeneousEM _)
    (funExt λ x → lem f x)
  where
  lem : (f : EM ℤ/2 1 → EM ℤ/2 n)
        (x : EM ℤ/2 1)
    → PathP (λ i → EM ℤ/2 (+'-comm n 1 i))
             (f x ⌣[ ℤ/2Ring R]ₖ x) (x ⌣[ ℤ/2Ring R]ₖ f x)
  lem f x = toPathP (sym (⌣ₖ-commℤ/2 1 n x (f x)))

⌣RP∞IsEq : (n : ℕ) → isEquiv (⌣RP∞ n)
⌣RP∞IsEq n =
  subst isEquiv
    (funExt (λ f → →∙Homogeneous≡ (isHomogeneousEM _)
      (λ i x → f x ⌣[ ℤ/2Ring R]ₖ (eRP∞-lem x i))))
      (ϕ-raw-contrRP∞ n .snd)
  where
  help : (g : _) → (λ i → eRP∞ (emloop g i) .fst .fst south)
                  ≡ emloop g
  help g j i =
    hcomp (λ k → λ {(i = i0) → embase
                   ; (i = i1) → emloop g k
                   ; (j = i0) → eRP∞ (emloop g i) .fst .fst
                                  (merid (λ w → emloop g (i ∧ w)) k)
                   ; (j = i1) → emloop g (i ∧ k)})
          (eRP∞ (emloop g i) .fst .snd j)

  eRP∞-lem : (x : _) → eRP∞ x .fst .fst south ≡ x
  eRP∞-lem = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) j → help g j i }

abstract
  ⌣RP∞'IsEq : (n : ℕ) → isEquiv (⌣RP∞' n)
  ⌣RP∞'IsEq n = transport (λ i → isEquiv (⌣RP∞≡⌣RP∞' n i)) (⌣RP∞IsEq n)

⌣RP∞Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1))
fst (⌣RP∞Equiv n) = ⌣RP∞ n
snd (⌣RP∞Equiv n) = ⌣RP∞IsEq n

⌣RP∞'Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (1 +' n))
fst (⌣RP∞'Equiv n) = ⌣RP∞' n
snd (⌣RP∞'Equiv n) = ⌣RP∞'IsEq n


+'-suc₁ : (n : ℕ) → 1 +' n ≡ suc n
+'-suc₁ zero = refl
+'-suc₁ (suc n) = refl

⌣RP∞''Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (suc n))
⌣RP∞''Equiv n =
  compEquiv (⌣RP∞'Equiv n)
    (isoToEquiv (pre∘∙equiv
      ((pathToEquiv (cong (EM ℤ/2) (+'-suc₁ n)))
      , (subst-EM-0ₖ (+'-suc₁ n)))))

RP→Charac₀ : Iso (EM ℤ/2 1 → ℤ/2 .fst)
                  (ℤ/2 .fst)
Iso.fun RP→Charac₀ f = f embase
Iso.inv RP→Charac₀ a = λ _ → a
Iso.rightInv RP→Charac₀ a = refl
Iso.leftInv RP→Charac₀ f =
  funExt (EM→Prop _ 0 (λ _ → is-set (snd ℤ/2Ring) _ _) refl)

RP→EM-ℤ/2-CharacIso : (n : ℕ)
  → Iso (EM ℤ/2 1 → EM ℤ/2 n)
         ((EM ℤ/2) ˣ n)
RP→EM-ℤ/2-CharacIso zero = RP→Charac₀ -- RP→Charac₀
RP→EM-ℤ/2-CharacIso (suc n) =
  compIso (EM→-charac {A = EM∙ ℤ/2 1} (suc n))
          (prodIso
            (compIso help (RP→EM-ℤ/2-CharacIso n))
            idIso)
  where
  help : Iso (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (suc n))
             (EM ℤ/2 1 → EM ℤ/2 n)
  help = equivToIso (invEquiv (⌣RP∞''Equiv n))

∥EM-ℤ/2ˣ∥₀-Iso : (n : ℕ) → Iso ∥ EM ℤ/2 ˣ n ∥₂ (fst ℤ/2)
∥EM-ℤ/2ˣ∥₀-Iso zero = setTruncIdempotentIso (is-set (snd ℤ/2Ring))
∥EM-ℤ/2ˣ∥₀-Iso (suc n) =
  compIso
    (compIso
      setTruncOfProdIso
      (compIso (Σ-cong-iso-snd λ _
        → equivToIso
            (isContr→≃Unit (∣ 0ₖ (suc n) ∣₂
              , ST.elim (λ _ → isSetPathImplicit)
                (EM→Prop _ _ (λ _ → squash₂ _ _) refl))))
        rUnit×Iso))
    (∥EM-ℤ/2ˣ∥₀-Iso n)

⌣RP∞''Equiv∙ : (n : ℕ)
  → ⌣RP∞''Equiv n .fst (λ _ → 0ₖ n) ≡ const∙ _ _
⌣RP∞''Equiv∙ n = →∙Homogeneous≡ (isHomogeneousEM _)
  (funExt λ x → cong (subst (EM ℤ/2) (+'-suc₁ n)) (⌣ₖ-0ₖ 1 n x)
              ∙ subst-EM∙ (+'-suc₁ n) .snd)

cohomRP∞Iso : (n : ℕ) → Iso (coHom n ℤ/2 (EM ℤ/2 1)) (ℤ/2 .fst)
cohomRP∞Iso n = compIso (setTruncIso (RP→EM-ℤ/2-CharacIso n)) (∥EM-ℤ/2ˣ∥₀-Iso n)

RP→EM-ℤ/2-CharacIso∙ : (n : ℕ)
  → Iso.fun (RP→EM-ℤ/2-CharacIso n) (λ _ → 0ₖ n) ≡ EM-ℤ/2ˣ∙ n
RP→EM-ℤ/2-CharacIso∙ zero = refl
RP→EM-ℤ/2-CharacIso∙ (suc n) =
  ΣPathP (((cong (fun (RP→EM-ℤ/2-CharacIso n))
   (funExt λ x
  → cong (λ f → invEq (⌣RP∞''Equiv n) f x)
            (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt (λ x → rCancelₖ (suc n) (0ₖ (suc n)))))
   ∙ funExt⁻ (sym (cong (invEq (⌣RP∞''Equiv n)) (⌣RP∞''Equiv∙ n))) x
   ∙ λ i → retEq (⌣RP∞''Equiv n) (λ _ → 0ₖ n) i x))
   ∙ RP→EM-ℤ/2-CharacIso∙ n)
   , refl)

HⁿRP∞≅ℤ/2 : (n : ℕ) → AbGroupIso (coHomGr n ℤ/2 (EM ℤ/2 1)) ℤ/2
fst (HⁿRP∞≅ℤ/2 n) = cohomRP∞Iso n
snd (HⁿRP∞≅ℤ/2 n) = pres0→GroupIso (isoToEquiv (cohomRP∞Iso n)) (cohomRP∞Iso∙ n)
  where
  ∥EM-ℤ/2ˣ∥₀-Iso∙ : (n : ℕ) → Iso.fun (∥EM-ℤ/2ˣ∥₀-Iso n) ∣ EM-ℤ/2ˣ∙ n ∣₂ ≡ fzero
  ∥EM-ℤ/2ˣ∥₀-Iso∙ zero = refl
  ∥EM-ℤ/2ˣ∥₀-Iso∙ (suc n) = ∥EM-ℤ/2ˣ∥₀-Iso∙ n

  cohomRP∞Iso∙ : (n : ℕ) → cohomRP∞Iso n .fun (0ₕ n) ≡ fzero
  cohomRP∞Iso∙ n = cong (Iso.fun (∥EM-ℤ/2ˣ∥₀-Iso n) ∘ ∣_∣₂) (RP→EM-ℤ/2-CharacIso∙ n)
                 ∙ ∥EM-ℤ/2ˣ∥₀-Iso∙ n

-- makeSquare : (n : ℕ)
--     → (EM ℤ/2 1
--     → EM ℤ/2 n
--     → EM ℤ/2 (n +' n))
--     → (EM ℤ/2 n → (EM ℤ/2) ˣ (n +' n))
-- makeSquare n f y = Iso.fun (RP→EM-ℤ/2-CharacIso _) λ x → f x y

-- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) where
--   UnordSmash∙² : Pointed ℓ
--   UnordSmash∙² = UnordSmash∙ X (λ x → UnordSmash∙ Y (A x))

--   UnordSmash∙²-fun : ((x : fst X) (y : fst Y) → A x y .fst)
--     → UnordSmash∙² .fst
--   UnordSmash∙²-fun f = inr (λ x → inr (f x))

-- -- open import Cubical.HITs.Join
-- -- ×⁴ : ∀ {ℓ} (A : Bool → Bool → Pointed ℓ) → Type ℓ
-- -- ×⁴ A = A true true .fst × A true false .fst
-- --      × A false true .fst × A false false .fst

-- -- module _ {ℓ} {A : Type ℓ} {B C : A → Type ℓ} (contr : isContr (Σ A B)) where
-- --   private
-- --     push-c : (a : A) (p : contr .fst .fst ≡ a)
-- --           → (c : C a)
-- --           → Path (cofib {A = C (contr .fst .fst)} {B = Σ A C} λ x → _ , x) (inl tt) (inr (a , c))
-- --     push-c = J> push

-- --     cofib→join : (ptA : A) (ptB : B ptA) → (cofib {A = C ptA} {B = Σ A C} λ x → _ , x) → Σ[ a ∈ A ] join (B a) (C a)
-- --     cofib→join ptA ptB (inl x) = ptA , (inl ptB) -- contr .fst .fst , inl (contr .fst .snd)
-- --     cofib→join ptA ptB (inr (a , c)) = a , inr c
-- --     cofib→join ptA ptB (push a i) = ptA , push ptB a i

-- --     push-c-coh : (a : A) (p : contr .fst .fst ≡ a) (d : B a) (pp : PathP (λ i → B (p i)) (contr .fst .snd) d) (c : C a)
-- --               → PathP (λ i → cofib→join (contr .fst .fst) (contr .fst .snd) (push-c a p c i) ≡ (a , push d c i))
-- --                        (ΣPathP (p , (λ j → inl (pp j))))
-- --                        refl -- refl
-- --     push-c-coh =
-- --       J> (J> λ c → flipSquare ((λ j i → cofib→join (contr .fst .fst) (contr .fst .snd) (help c j i))
-- --         ◁ λ i j → (contr .fst .fst) , (push (contr .fst .snd) c j)))
-- --       where
-- --       help : (c : _) → push-c (contr .fst .fst) refl c ≡ push c
-- --       help = funExt⁻ (transportRefl push)

-- --   joinC : Iso (Σ[ a ∈ A ] join (B a) (C a))
-- --               (cofib {A = C (contr .fst .fst)} {B = Σ A C} λ x → _ , x)
-- --   Iso.fun joinC (a , inl x) = inl tt
-- --   Iso.fun joinC (a , inr x) = inr (a , x)
-- --   Iso.fun joinC (a , push b c i) = push-c a (cong fst (contr .snd (a , b))) c i
-- --   Iso.inv joinC = cofib→join (contr .fst .fst) (contr .fst .snd)
-- --   Iso.rightInv joinC (inl x) = refl
-- --   Iso.rightInv joinC (inr x) = refl
-- --   Iso.rightInv joinC (push a i) j =
-- --     ((λ j → push-c (contr .fst .fst)
-- --              (cong fst (isProp→isSet (isContr→isProp contr) _ _ (contr .snd (contr .fst)) refl j)) a)
-- --      ∙ lem a) j i
-- --     where
-- --     lem : (a : _) → Path (Path (cofib (λ x → contr .fst .fst , x)) _ _) (push-c (contr .fst .fst) refl a) (push a)
-- --     lem = funExt⁻ (transportRefl push)
-- --   Iso.leftInv joinC (a , inl x) = ΣPathP ((cong fst (contr .snd (a , x))) , (λ j → inl (contr .snd (a , x) j .snd)))
-- --   Iso.leftInv joinC (a , inr x) = refl
-- --   Iso.leftInv joinC (a , push c d i) j =
-- --     push-c-coh a (cong fst (contr .snd (a , c))) c (cong snd (contr .snd (a , c))) d i j

-- -- JoinStructureBool : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- --   (f : A true true .fst × A true false .fst
-- --      × A false true .fst × A false false .fst
-- --     → fst B)
-- --   → Type
-- -- JoinStructureBool A B f =
-- --   (g : A true true .fst × A true false .fst
-- --      × A false true .fst × A false false .fst)
-- --   → join (join (fst g ≡ A true true .snd)
-- --                 (snd g .fst ≡ A true false .snd))
-- --           (join (snd (snd g) .fst ≡ A false true .snd)
-- --                 (snd (snd g) .snd ≡ A false false .snd))
-- --   → f g ≡ B .snd

-- -- module DEP (A B :  Pointed ℓ-zero) (T : fst A → fst B → Pointed ℓ-zero)
-- --          (f : (a : fst A) (b : fst B) → fst (T a b)) where
-- --   JS₁ : Type
-- --   JS₁ = (a : A .fst) (b : B .fst)
-- --       → join (a ≡ A .snd) (b ≡ B .snd)
-- --       → f a b ≡ T a b .snd

-- --   JS'l : singl (pt A) → Type
-- --   JS'l (a , p) = (b : fst B) → f a b ≡ T a b .snd

-- --   JS'r : singl (pt B) → Type
-- --   JS'r (b , p) = (a : fst A) → f a b ≡ T a b .snd

-- --   JS₁' : Type
-- --   JS₁' = Σ[ l ∈ ((a : _) → JS'l a) ]
-- --          Σ[ r ∈ ((a : _) → JS'r a) ]
-- --          ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))


-- --   JS₁'' : Type
-- --   JS₁'' = Σ[ l ∈ JS'l (pt A , refl) ]
-- --           Σ[ r ∈ JS'r (pt B , refl) ]
-- --           l (pt B) ≡ r (pt A)

-- --   IS1 : Iso JS₁ JS₁'
-- --   fst (Iso.fun IS1 F) (a , p) b = F a b (inl (sym p))
-- --   fst (snd (Iso.fun IS1 F)) (b , p) a = F a b (inr (sym p))
-- --   snd (snd (Iso.fun IS1 F)) (a , p) (b , q) = cong (F a b) (push (sym p) (sym q))
-- --   Iso.inv IS1 (l , r , lr) a b (inl x) = l (a , sym x) b
-- --   Iso.inv IS1 (l , r , lr) a b (inr x) = r (b , sym x) a
-- --   Iso.inv IS1 (l , r , lr) a b (push p q i) = lr (a , sym p) (b , sym q) i
-- --   Iso.rightInv IS1 _ = refl
-- --   Iso.leftInv IS1 F = funExt λ a → funExt λ b → funExt
-- --     λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

-- --   IS2 : Iso JS₁' JS₁''
-- --   IS2 = compIso
-- --     (Σ-cong-iso
-- --       {B = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
-- --                    ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))}
-- --       {B' = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
-- --                    ((b : _) → l (fst b) ≡ r b (pt A))}
-- --       (DomainContrIso (isContrSingl (pt A)))
-- --         λ x → Σ-cong-iso-snd λ r → DomainContrIso (isContrSingl (pt A)))
-- --       (Σ-cong-iso-snd
-- --         λ l → Σ-cong-iso {B = λ r → ((b : _) → l (fst b) ≡ r b (pt A))}
-- --                           {B' = λ r → (l (pt B) ≡ r (pt A))}
-- --       (DomainContrIso (isContrSingl (pt B)))
-- --       λ _ → DomainContrIso (isContrSingl (pt B)))

-- --   FullIso : Iso JS₁ JS₁''
-- --   FullIso = compIso IS1 IS2

-- -- move later
-- -- RP∞'→SetElim :
-- --   ∀ {ℓ} {A : RP∞' ℓ → Type ℓ} (s : (X : _) → isSet (A X))
-- --      → (f : (X : RP∞' ℓ) → fst X → A X)
-- --      → ((X : RP∞' ℓ) → (x : fst X) → f X x ≡ f X (RP∞'-fields.notRP∞' X x))
-- --      → ((X : RP∞' ℓ) → A X)
-- -- RP∞'→SetElim {A = A} s f f-comm =
-- --   uncurry λ X → uncurry λ 2tx
-- --   → elim→Set (λ _ → s _)
-- --        (λ x → f (X , 2tx , ∣ x ∣₁) x)
-- --        λ x → RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
-- --               (λ i → f (X , 2tx , squash₁ ∣ x ∣₁ ∣ x ∣₁ i) x)
-- --               (f-comm (X , 2tx , ∣ x ∣₁) x
-- --             ◁ λ i → f (X , 2tx , squash₁ ∣ x ∣₁ ∣ fst 2tx x ∣₁ i) (fst 2tx x))

-- -- RP∞'→SetElimEq :
-- --   ∀ {ℓ} {A : RP∞' ℓ → Type ℓ} (s : (X : _) → isSet (A X))
-- --      (f : (X : RP∞' ℓ) → fst X → A X)
-- --      (h : (X : RP∞' ℓ) → (x : fst X) → f X x ≡ f X (RP∞'-fields.notRP∞' X x))
-- --      (X : RP∞' ℓ) (x : _)
-- --      → RP∞'→SetElim s f h X ≡ f X x
-- -- RP∞'→SetElimEq {A = A} s f h = uncurry λ X → uncurry
-- --   λ 2x → PT.elim (λ _ → isPropΠ λ _ → s _ _ _)
-- --     λ x → RP∞'-fields.elimRP∞' (X , 2x , ∣ x ∣₁) x
-- --             (fromPathP λ i → (f (X , 2x , squash₁ ∣ x ∣₁ ∣ x ∣₁ i)  x))
-- --             (fromPathP (h (X , 2x , ∣ x ∣₁) x
-- --               ◁ λ i → f (X , 2x , squash₁ ∣ x ∣₁ ∣ x ∣₁ i) (fst 2x x)))

-- RP∞'→SetRec : ∀ {ℓ} {A : Type ℓ} (s : isSet A) (X : RP∞' ℓ)
--          → (f : fst X → A)
--          → ((x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
--          → A
-- RP∞'→SetRec s = uncurry λ X
--   → uncurry λ 2tx
--   → elim→Set (λ _ → isSetΠ2 λ _ _ → s)
--                (λ x f coh → f x)
--                λ x → RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
--                  (λ i f coh → f x)
--                  λ i f coh → coh x i

-- RP∞'→SetRecEq :
--   ∀ {ℓ} {A : Type ℓ} (s : isSet A) (X : _)
--      (f : fst X → A)
--      (h : (x : fst X) → f x ≡ f (RP∞'-fields.notRP∞' X x))
--      (x : fst X)
--      → RP∞'→SetRec s X f h ≡ f x
-- RP∞'→SetRecEq {A = A} s = uncurry λ X → uncurry
--   λ 2x → PT.elim (λ _ → isPropΠ3 λ _ _ _ → s _ _)
--     λ x f h → RP∞'-fields.elimRP∞' (X , 2x , ∣ x ∣₁) x
--       (λ i → transportRefl (transportRefl (f (transportRefl x i)) i) i)
--       ((λ i → transportRefl (transportRefl (f (transportRefl x i)) i) i) ∙ h x)


-- abstract
--   notNotRP∞' : ∀ {ℓ} (X : RP∞' ℓ) (x : fst X)
--     → RP∞'-fields.notRP∞' X (RP∞'-fields.notRP∞' X x) ≡ x
--   notNotRP∞' = JRP∞' refl

-- RP∞'→GroupoidRec : ∀ {ℓ} {A : Type ℓ} (s : isGroupoid A) (X : RP∞' ℓ)
--          → (f : fst X → A)
--          → (f-coh : (x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
--          → (p : (x : fst X)
--            → PathP (λ i → f (notNotRP∞' X x (~ i)) ≡ f (RP∞'-fields.notRP∞' X x))
--                     (f-coh x)
--                     (sym (f-coh (RP∞'-fields.notRP∞' X x))))
--          → A
-- RP∞'→GroupoidRec {ℓ = ℓ} {A = A} grA = uncurry λ X
--   → uncurry λ 2tx
--   → elim→Gpd _ (λ _ → isGroupoidΠ3 λ _ _ _ → grA)
--       (F1 X 2tx)
--       (F2 X 2tx)
--       λ x → F3 (X , 2tx , ∣ x ∣₁) x
--   where
--   F1 : (X : Type) (2tx : is2Type ℓ X) (x : X) (f : X → A)
--        (f-coh : (x' : X) → f x' ≡ f (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x')) →
--       ((x' : X) →
--        PathP (λ i → f (notNotRP∞' (X , 2tx , ∣ x ∣₁) x' (~ i))
--                    ≡ f (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x'))
--              (f-coh x')
--              (sym (f-coh (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x'))))
--       → A
--   F1 X 2tx x f coh p = f x

--   F2 : (X : Type) (2tx : is2Type ℓ X) (x y : X) →
--       PathP (λ i →
--             (f : X → A)
--             (f-coh : (x' : X)
--              → f x' ≡ f (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x'))
--         → ((x' : X) →
--           PathP (λ i₁ →
--              f (notNotRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x' (~ i₁))
--            ≡ f (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x'))
--           (f-coh x')
--           (sym (f-coh (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x')))) → A)
--           (F1 X 2tx x)
--           (F1 X 2tx y)
--   F2 X 2tx x =
--     RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
--       (λ i f coh p → f x)
--       λ i f coh p → coh x i

--   F3 : (X : RP∞' ℓ) (x y z : fst X) →
--       SquareP
--         (λ i j → (f : fst X → A)
--                   (f-coh : (x' : fst X)
--                 → f x'
--                  ≡ f (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x'))
--          → ((x' : fst X) →
--           PathP
--           (λ i₁ →
--              f (notNotRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x' (~ i₁))
--            ≡ f (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x'))
--           (f-coh x')
--           (sym (f-coh (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x')))) → A)
--       (F2 (fst X) (fst (snd X)) x y) (F2 (fst X) (fst (snd X)) x z)
--       (λ i f f-coh p → f x) (F2 (fst X) (fst (snd X)) y z)
--   F3 = JRP∞' (CasesBool true
--         (CasesBool true (λ i j f f-coh _ → f true)
--                         λ i j f f-coh p → f-coh true (i ∧ j))
--         (CasesBool true
--           (λ i j f f-coh p
--             → hcomp (λ k → λ {(i = i0) → p true (~ k) j
--                               ; (i = i1) → f true --  f-coh false (k ∧ j) -- f true
--                               ; (j = i0) → f (notNotRP∞' (RP∞'∙ ℓ) true (k ∨ i))
--                               ; (j = i1) → f-coh false i})
--                 (hcomp (λ k → λ {(i = i0) → f-coh false (~ j)
--                                 ; (i = i1) → f true
--                                 ; (j = i0) → f (isSetBool _ _ refl (notNotRP∞' (RP∞'∙ ℓ) true) k i)
--                                 ; (j = i1) → f-coh false i})
--                        (f-coh false (i ∨ ~ j))))
--           λ i j f f-coh p → f-coh true j))

-- RP∞'→GroupoidRecId : ∀ {ℓ} {A : Type ℓ} (s : isGroupoid A) (X : RP∞' ℓ)
--    → (f : fst X → A)
--    → (f-coh : (x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
--    → (p : (x : fst X)
--      → PathP (λ i → f (notNotRP∞' X x (~ i)) ≡ f (RP∞'-fields.notRP∞' X x))
--               (f-coh x)
--               (sym (f-coh (RP∞'-fields.notRP∞' X x))))
--    → Σ[ f-id ∈ ((x : fst X) → RP∞'→GroupoidRec s X f f-coh p ≡ f x) ]
--         ((x : fst X) → PathP (λ i → {!!}) {!!} {!!}) -- (RP∞'→GroupoidRec s X f f-coh p) (RP∞'→GroupoidRec s X f f-coh p))
-- RP∞'→GroupoidRecId = {!!}

-- isGroupoidRP∞' : isGroupoid (RP∞' ℓ-zero)
-- isGroupoidRP∞' = {!!}

-- EM₁-ℤ/2→RP∞'-emloop : (g : ℤ/2 .fst) → RP∞'∙ ℓ-zero ≡ RP∞'∙ ℓ-zero
-- EM₁-ℤ/2→RP∞'-emloop (zero , p) = refl
-- EM₁-ℤ/2→RP∞'-emloop (suc zero , p) = Σ≡Prop (isPropIsRP∞ ℓ-zero) (ua notEquiv)
-- EM₁-ℤ/2→RP∞'-emloop (suc (suc g) , p) =
--   ⊥.rec (¬-<-zero (<-k+-cancel {k = 2} p))

-- EM₁-ℤ/2→RP∞' : EM ℤ/2 1 → RP∞' ℓ-zero
-- EM₁-ℤ/2→RP∞' =
--   elimGroupoid _ (λ _ → isGroupoidRP∞') (RP∞'∙ ℓ-zero)
--     EM₁-ℤ/2→RP∞'-emloop
--     λ g h → ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ-zero _))
--       (coh g h)
--   where
--   coh : (g h : ℤ/2 .fst)
--     → Square refl (cong fst (EM₁-ℤ/2→RP∞'-emloop h))
--              (cong fst (EM₁-ℤ/2→RP∞'-emloop g))
--              (cong fst (EM₁-ℤ/2→RP∞'-emloop (g +ₘ h)))
--   coh = ℤ/2-elim (ℤ/2-elim refl λ i j → ua notEquiv (i ∧ j))
--                  (ℤ/2-elim (λ i j → ua notEquiv i)
--                            ((λ i j → ua notEquiv (~ j ∧ i)) ▷ sym help))
--     where
--     help : ua notEquiv ≡ sym (ua notEquiv)
--     help = cong ua (Σ≡Prop isPropIsEquiv (funExt (CasesBool true refl refl)))
--           ∙ uaInvEquiv notEquiv

-- RP∞'→EM₁-ℤ/2' : EM ℤ/2 1 ≃ RP∞' ℓ-zero
-- RP∞'→EM₁-ℤ/2' = EM₁-ℤ/2→RP∞'
--   , record { equiv-proof = RP∞'pt→Prop (λ _ → isPropIsContr)
--              ((embase , refl)
--            , (isEmbedding→hasPropFibers′ {f = EM₁-ℤ/2→RP∞'}
--                (Cubical.HITs.EilenbergMacLane1.elimProp _ (λ _ → isPropΠ λ _ → isPropIsEquiv _)
--                  (Cubical.HITs.EilenbergMacLane1.elimProp _ (λ _ → isPropIsEquiv _)
--                    (subst isEquiv (sym main) (isoToEquiv (invIso (compIso p2 p1)) .snd )))) _ _)) }
--   where --
--   p1 : Iso Bool (Ω (EM∙ ℤ/2 1) .fst)
--   p1 = compIso (fst Bool≅ℤGroup/2) (Iso-EM-ΩEM+1 0)

--   is1 : Iso (RP∞'∙ ℓ-zero ≡ RP∞'∙ ℓ-zero) (Bool ≡ Bool)
--   fun is1 = cong fst
--   inv is1 p = Σ≡Prop (isPropIsRP∞ ℓ-zero) p
--   rightInv is1 p = refl
--   leftInv is1 p =
--     ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ-zero _))
--       λ i j → fst (p j)

--   p2 : Iso (Ω (RP∞' ℓ-zero , RP∞'∙ ℓ-zero) .fst) Bool
--   p2 = compIso is1 (compIso (equivToIso univalence) Bool≃Charac)

--   main : cong EM₁-ℤ/2→RP∞' ≡ Iso.inv p2 ∘ Iso.inv p1
--   main = funExt λ x → cong (cong EM₁-ℤ/2→RP∞') (sym (Iso.rightInv p1 x))
--                      ∙ sym (Iso.leftInv p2 _)
--                      ∙ cong (Iso.inv p2) (is3 (Iso.inv p1 x))
--     where
--     is3 : (x : Bool) → Iso.fun p2 (cong EM₁-ℤ/2→RP∞' (Iso.fun p1 x)) ≡ x
--     is3 false = refl
--     is3 true = refl


--   {-
--   help : (X : RP∞' ℓ-zero) → isContr (Σ[ X' ∈ (EM ℤ/2 1) ] EM₁-ℤ/2→RP∞' X' ≡ X)
--   help =
--     RP∞'pt→Prop (λ _ → isPropIsContr) ((embase , refl)
--     , (uncurry (elimSet _ (λ _ → isSetΠ λ _
--       → isOfHLevelPath' 2
--           (isOfHLevelΣ 3 emsquash (λ _ → isOfHLevelPath 3 isGroupoidRP∞' _ _)) _ _)
--       (λ y → p1 {!!})
--       {!!})))
--     where
--     fibr = Σ[ X' ∈ (EM ℤ/2 1) ] EM₁-ℤ/2→RP∞' X' ≡ RP∞'∙ ℓ-zero


--     uap' : Bool → RP∞'∙ ℓ-zero ≡ RP∞'∙ ℓ-zero
--     uap' false = Σ≡Prop (isPropIsRP∞ ℓ-zero) (ua notEquiv)
--     uap' true = refl

--     uapEq : Bool ≃ (RP∞'∙ ℓ-zero ≡ RP∞'∙ ℓ-zero)
--     fst uapEq = uap'
--     snd uapEq = subst isEquiv (funExt l) (isoToEquiv (invIso uap) .snd)
--       where


--       l : (x : _) → inv uap x ≡ uap' x
--       l false = refl
--       l true = ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ-zero _))
--                 (uaIdEquiv)

--     p1 : (e : Bool) → Path fibr (embase , refl) (embase , uap' e)
--     p1 false = ΣPathP ((emloop fone) ,
--       (ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ-zero _))
--         ((λ i j → ua (notEquiv) (i ∧ ~ j))
--         ▷ (sym (uaInvEquiv notEquiv) ∙ cong ua (Σ≡Prop isPropIsEquiv refl)))))
--     p1 true = refl

--     r : (e : RP∞'∙ ℓ-zero ≡ RP∞'∙ ℓ-zero)
--       → Σ[ f ∈ Path fibr (embase , refl) (embase , e) ]
--           {!(g : ℤ/2) → PathP !}
--     r = {!!}
-- -}


-- RP∞'→EM₁-ℤ/2 : RP∞' ℓ-zero → EM ℤ/2 1
-- RP∞'→EM₁-ℤ/2 X =
--   RP∞'→GroupoidRec emsquash X (λ _ → embase)
--                     (λ x → {!!})
--                     {!!}

-- -- ∑RP∞' : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → ℕ
-- -- ∑RP∞' X n =
-- --   RP∞'→SetRec isSetℕ X
-- --    (λ x → n x +' n (RP∞'-fields.notRP∞' X x))
-- --    λ x → +'-comm (n x) _ ∙ cong (n (RP∞'-fields.notRP∞' X x) +'_)
-- --                            (cong n (sym (notNotRP∞' X x)))


-- -- ∑RP∞'≡ : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
-- --   → ∑RP∞' X n ≡ n x +' n (RP∞'-fields.notRP∞' X x)
-- -- ∑RP∞'≡ = RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isSetℕ _ _)
-- --   λ { false n → +'-comm (n true) (n false)
-- --      ; true n → refl}

-- -- ∑RP∞'Fubini : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → (∑RP∞' Y (λ y → ∑RP∞' X (λ x → n x y)))
-- --    ≡ (∑RP∞' X (λ x → ∑RP∞' Y (n x)))
-- -- ∑RP∞'Fubini =
-- --   RP∞'pt→Prop (λ X → isPropΠ2 λ _ _ → isSetℕ _ _)
-- --     (RP∞'pt→Prop ((λ _ → isPropΠ λ _ → isSetℕ _ _))
-- --       λ n → move4 (n true true) (n false true) (n true false) (n false false) _+'_
-- --         +'-assoc
-- --         +'-comm)

-- -- module _ {ℓ} (X : RP∞' ℓ) (A : fst X → Pointed ℓ) (B : Pointed ℓ) where
-- --   BipointedUnordJoin : (f : ((x : fst X) → A x .fst) → fst B) → Type ℓ
-- --   BipointedUnordJoin f =
-- --       (g : (x : fst X) → A x .fst)
-- --     → UnordJoinR X (λ x → g x ≡ A x .snd)
-- --     → f g ≡ B .snd


-- -- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Pointed ℓ) where
-- --   QuadpointedUnordJoin : (f : ((x : fst X) (y : fst Y) → A x y .fst) → fst B) → Type ℓ
-- --   QuadpointedUnordJoin f = (g : (x : fst X) (y : fst Y) → A x y .fst)
-- --     → UnordJoinR X (λ x → UnordJoinR Y λ y → g x y ≡ A x y .snd)
-- --     → f g ≡ B .snd

-- -- open import Cubical.HITs.Join
-- -- module _ {ℓ} (A B T :  Pointed ℓ)
-- --          (f : fst A → fst B → fst T) where
-- --   BipointedJoinBool : Type ℓ
-- --   BipointedJoinBool = (a : A .fst) (b : B .fst)
-- --       → join (a ≡ A .snd) (b ≡ B .snd)
-- --       → f a b ≡ T .snd

-- --   JS'l : singl (pt A) → Type ℓ
-- --   JS'l (a , p) = (b : fst B) → f a b ≡ T .snd

-- --   JS'r : singl (pt B) → Type ℓ
-- --   JS'r (b , p) = (a : fst A) → f a b ≡ T .snd

-- --   BipointedJoinBool' : Type ℓ
-- --   BipointedJoinBool' = Σ[ l ∈ ((a : _) → JS'l a) ]
-- --          Σ[ r ∈ ((a : _) → JS'r a) ]
-- --          ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))


-- --   BipointedJoinBool'' : Type ℓ
-- --   BipointedJoinBool'' = Σ[ l ∈ JS'l (pt A , refl) ]
-- --           Σ[ r ∈ JS'r (pt B , refl) ]
-- --           l (pt B) ≡ r (pt A)

-- --   IS1 : Iso BipointedJoinBool BipointedJoinBool'
-- --   fst (Iso.fun IS1 F) (a , p) b = F a b (inl (sym p))
-- --   fst (snd (Iso.fun IS1 F)) (b , p) a = F a b (inr (sym p))
-- --   snd (snd (Iso.fun IS1 F)) (a , p) (b , q) = cong (F a b) (push (sym p) (sym q))
-- --   Iso.inv IS1 (l , r , lr) a b (inl x) = l (a , sym x) b
-- --   Iso.inv IS1 (l , r , lr) a b (inr x) = r (b , sym x) a
-- --   Iso.inv IS1 (l , r , lr) a b (push p q i) = lr (a , sym p) (b , sym q) i
-- --   Iso.rightInv IS1 _ = refl
-- --   Iso.leftInv IS1 F = funExt λ a → funExt λ b → funExt
-- --     λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

-- --   IS2 : Iso BipointedJoinBool' BipointedJoinBool''
-- --   IS2 = compIso
-- --     (Σ-cong-iso
-- --       {B = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
-- --                    ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))}
-- --       {B' = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
-- --                    ((b : _) → l (fst b) ≡ r b (pt A))}
-- --       (DomainContrIso (isContrSingl (pt A)))
-- --         λ x → Σ-cong-iso-snd λ r → DomainContrIso (isContrSingl (pt A)))
-- --       (Σ-cong-iso-snd
-- --         λ l → Σ-cong-iso {B = λ r → ((b : _) → l (fst b) ≡ r b (pt A))}
-- --                           {B' = λ r → (l (pt B) ≡ r (pt A))}
-- --       (DomainContrIso (isContrSingl (pt B)))
-- --       λ _ → DomainContrIso (isContrSingl (pt B)))

-- --   FullIso : Iso BipointedJoinBool BipointedJoinBool''
-- --   FullIso = compIso IS1 IS2

-- -- module _ (A B C D T :  Pointed ℓ-zero)
-- --          (f : fst A → fst B → fst C → fst D → fst T) where
-- --   JS4 : Type
-- --   JS4 = (a : fst A) (b : fst B) (c : fst C) (d : fst D)
-- --       → join (join (a ≡ snd A) (b ≡ snd B)) (join (c ≡ snd C) (d ≡ snd D))
-- --       → f a b c d ≡ pt T

-- -- open import Cubical.HITs.SmashProduct

-- -- isOfHLevelEM→ : ∀ {ℓ} {G H : AbGroup ℓ} (n : ℕ)
-- --   → isOfHLevel 3 (EM∙ G n →∙ EM∙ H (suc n))
-- -- isOfHLevelEM→ {G = G} {H = H} n =
-- --   isConnected→∙ (suc n) 2 (isConnectedEM n)
-- --     (subst (λ m → isOfHLevel m (EM H (suc n))) (+-comm 2 (suc n))
-- --       (hLevelEM _ (suc n)))

-- -- mainLem' : (A B T : Pointed ℓ-zero)
-- --   → Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
-- --           (A ⋀∙ B →∙ T)
-- -- mainLem' A B T = compIso (Σ-cong-iso-snd (λ f → FullIso A B T f)) is2
-- --   where
-- --   F→ : (T : Type) (t : T) → Σ[ f ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , t) f → (A ⋀∙ B →∙ (T , t))
-- --   fst (F→ T t (f , fl , fr , flr)) (inl x) = t
-- --   fst (F→ T t (f , fl , fr , flr)) (inr x) = f (fst x) (snd x)
-- --   fst (F→ T t (f , fl , fr , flr)) (push (inl x) i) = fr x (~ i)
-- --   fst (F→ T t (f , fl , fr , flr)) (push (inr x) i) = fl x (~ i)
-- --   fst (F→ T t (f , fl , fr , flr)) (push (push a i₁) i) = flr (~ i₁) (~ i)
-- --   snd (F→ T t (f , fl , fr , flr)) = refl

-- --   mmB : (T : Type) (f : A ⋀ B → T)
-- --     → Σ[ g ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , f (inl tt)) g
-- --   fst (mmB T f) a b = f (inr (a , b))
-- --   fst (snd (mmB T f)) b = cong f (sym (push (inr b)))
-- --   fst (snd (snd (mmB T f))) c = cong f (sym (push (inl c)))
-- --   snd (snd (snd (mmB T f))) j i = f (push (push tt (~ j)) (~ i))

-- --   mm' : (T : Type) (f : A ⋀ B → T) (t : T)
-- --     → (f (inl tt) ≡ t)
-- --     → BipointedJoinBool'' A B (T , t) (λ a b → f (inr (a , b)))
-- --   mm' T f = J> mmB T f .snd

-- --   mm : (T : Type) (f : A ⋀ B → T) (t : T)
-- --     → (f (inl tt) ≡ t)
-- --     → Σ[ f ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , t) f
-- --   fst (mm T f t x) a b = f (inr (a , b))
-- --   snd (mm T f t x) = mm' T f t x

-- --   c1 : (T : Type) (f : A ⋀ B → T) (t : T) (p : f (inl tt) ≡ t)
-- --     → F→ T t (mm T f t p) ≡ (f , p)
-- --   c1 T f =
-- --     J> cong (F→ T (f (inl tt)))
-- --         (ΣPathP (refl , (transportRefl (mmB T f .snd))))
-- --      ∙ ΣPathP ((funExt (
-- --              λ { (inl x) → refl
-- --                ; (inr x) → refl
-- --                ; (push (inl x) i) → refl
-- --                ; (push (inr x) i) → refl
-- --                ; (push (push a i₁) i) → refl})) , refl)

-- --   is2 : Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool'' A B T f)
-- --             (A ⋀∙ B →∙ T)
-- --   Iso.fun is2 f = F→ (fst T) (snd T) f
-- --   Iso.inv is2 f = mm (fst T) (fst f) (snd T) (snd f)
-- --   Iso.rightInv is2 f = c1 (fst T) (fst f) _ (snd f)
-- --   Iso.leftInv is2 f = ΣPathP (refl , transportRefl (snd f))

-- -- mainLem : (A B T : Pointed ℓ-zero)
-- --   → Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
-- --          (A →∙ (B →∙ T ∙))
-- -- mainLem A B T = compIso (mainLem' A B T) SmashAdjIso

-- -- open Iso
-- -- open import Cubical.Foundations.Equiv.HalfAdjoint


-- -- Iso-BipointedUnordJoin-BipointedJoinBool :
-- --   ∀ {ℓ} (A : Bool → Pointed ℓ) (B : Pointed ℓ)
-- --   → (f : ((x : Bool) → A x .fst) → fst B)
-- --   → Iso (BipointedUnordJoin (RP∞'∙ ℓ) A B f)
-- --          (BipointedJoinBool (A true) (A false) B
-- --            λ a b → f (CasesBool true a b))
-- -- Iso-BipointedUnordJoin-BipointedJoinBool A B f =
-- --   compIso (codomainIsoDep (λ g → domIso join-UnordJoinR-iso))
-- --     (compIso (ΠIso ΠBool×Iso λ g
-- --       → codomainIso (pathToIso (cong (_≡ B .snd) (cong f (sym (CasesBoolη g)))))) curryIso)

-- -- SteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → Type
-- -- SteenrodFunType X n =
-- --   Σ[ f ∈ (((x : fst X) → EM ℤ/2 (n x)) → EM ℤ/2 (∑RP∞' X n)) ]
-- --     BipointedUnordJoin X (λ x → EM∙ ℤ/2 (n x)) (EM∙ ℤ/2 (∑RP∞' X n)) f

-- -- isSetSteenrodFunTypeBoolIso : (n : Bool → ℕ)
-- --   → Iso (SteenrodFunType (RP∞'∙ ℓ-zero) n)
-- --          (EM∙ ℤ/2 (n true) →∙ (EM∙ ℤ/2 (n false) →∙ EM∙ ℤ/2 (n true +' n false) ∙))
-- -- isSetSteenrodFunTypeBoolIso n =
-- --   (compIso (Σ-cong-iso-snd (λ f → Iso-BipointedUnordJoin-BipointedJoinBool _ _ _))
-- --              (compIso (invIso (Σ-cong-iso (compIso (invIso curryIso) (invIso (ΠIso ΠBool×Iso λ f → idIso)))
-- --                       λ g → idIso))
-- --              (mainLem (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
-- --                       (EM∙ ℤ/2 (n true +' n false)))))

-- -- isSetSteenrodFunTypeBoolIsoId : (n : Bool → ℕ) (f : _) (x : _) (y : _)
-- --   →  Iso.fun (isSetSteenrodFunTypeBoolIso n) f .fst x .fst y ≡ fst f (×→ΠBool (x , y))
-- -- isSetSteenrodFunTypeBoolIsoId n f x y = transportRefl _

-- -- isSetSteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → isSet (SteenrodFunType X n)
-- -- isSetSteenrodFunType = RP∞'pt→Prop (λ _ → isPropΠ λ _ → isPropIsOfHLevel 2)
-- --   λ n → isOfHLevelRetractFromIso 2
-- --     (isSetSteenrodFunTypeBoolIso n)
-- --     (isConnected→∙ (suc (n true)) 1
-- --     (isConnectedEM (n true))
-- --     (subst (λ m → isOfHLevel m (EM∙ ℤ/2 (n false) →∙ EM∙ ℤ/2 (n true +' n false)))
-- --            (cong suc (+-comm 1 (n true)) )
-- --            (isConnected→∙ (suc (n false)) (suc (n true))
-- --              (isConnectedEM (n false))
-- --              (subst (λ m → isOfHLevel (suc m) (EM ℤ/2 (n true +' n false)))
-- --                 (cong suc (+'≡+ (n true) (n false)) ∙ (+-comm (suc (n true)) (n false)))
-- --                 (hLevelEM ℤ/2 (n true +' n false))))))

-- -- SteenrodFunType≡ : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
-- --   (f g : SteenrodFunType X n)
-- --   → fst f ≡ fst g
-- --   → f ≡ g
-- -- SteenrodFunType≡ =
-- --   RP∞'pt→Prop (λ X → isPropΠ4 λ n _ _ _ → isSetSteenrodFunType X n _ _)
-- --    λ n f g p → sym (Iso.leftInv (isSetSteenrodFunTypeBoolIso n) f)
-- --             ∙∙ cong (inv (isSetSteenrodFunTypeBoolIso n))
-- --                  (→∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
-- --                    (funExt (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
-- --                      (funExt λ y → transportRefl _
-- --                                   ∙ funExt⁻ p (×→ΠBool (x , y))
-- --                                   ∙ sym (transportRefl _)))))
-- --             ∙∙ Iso.leftInv (isSetSteenrodFunTypeBoolIso n) g

-- -- cp : {n m : ℕ} → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n +' m)
-- -- cp = _⌣ₖ_ {G'' = ℤ/2Ring}

-- -- Sq : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
-- --        (f : ((x₁ : fst X) → EM ℤ/2 (n x₁))) → EM ℤ/2 (∑RP∞' X n)
-- -- Sq X x n f =
-- --   subst (EM ℤ/2) (sym (∑RP∞'≡ X x n))
-- --       (cp (f x) (f (RP∞'-fields.notRP∞' X x)))

-- -- Sq-bool : (n : Bool → ℕ) (f : ((x₁ : Bool) → EM ℤ/2 (n x₁)))
-- --   → EM ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n)
-- -- Sq-bool n f = cp (f true) (f false)

-- -- sq≡ : (n : Bool → ℕ) (f : ((x₁ : Bool) → EM ℤ/2 (n x₁)))
-- --   → Sq (RP∞'∙ ℓ-zero) true n f ≡ Sq-bool n f
-- -- sq≡ n f = (λ j → subst (EM ℤ/2)
-- --                      (isSetℕ _ _ (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n)) refl j)
-- --                      (Sq-bool n f))
-- --            ∙ transportRefl _


-- -- sq' : (n : Bool → ℕ)
-- --   → SmashPt (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
-- --   →∙ EM∙ ℤ/2 (n true +' n false)
-- -- fst (sq' n) basel = 0ₖ (n true +' n false)
-- -- fst (sq' n) baser = 0ₖ (n true +' n false)
-- -- fst (sq' n) (proj x y) = cp x y
-- -- fst (sq' n) (gluel a i) = ⌣ₖ-0ₖ {G'' = ℤ/2Ring} (n true) (n false) a i
-- -- fst (sq' n) (gluer b i) = 0ₖ-⌣ₖ {G'' = ℤ/2Ring} (n true) (n false) b i
-- -- snd (sq' n) = refl

-- -- sq-coh-bool : (n : Bool → ℕ)
-- --   → BipointedJoinBool (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
-- --                        (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n))
-- --          (λ a b → Sq-bool n (CasesBool true a b))
-- -- sq-coh-bool n =
-- --   mainLem' (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
-- --            (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n)) .Iso.inv
-- --     (sq' n ∘∙ (⋀→Smash , refl)) .snd

-- -- sq-coh : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
-- --   → BipointedUnordJoin X (λ x₁ → EM∙ ℤ/2 (n x₁))
-- --                           (EM∙ ℤ/2 (∑RP∞' X n)) (Sq X x n)
-- -- sq-coh = JRP∞' λ n → Iso-BipointedUnordJoin-BipointedJoinBool
-- --                         (λ x₁ → EM∙ ℤ/2 (n x₁))
-- --                         (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n))
-- --                         (Sq (RP∞'∙ ℓ-zero) true n) .Iso.inv
-- --                         λ g x r → sq≡ n _ ∙ sq-coh-bool n g x r

-- -- comm-field : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
-- --   → Path (SteenrodFunType X n)
-- --           (Sq X x n
-- --            , sq-coh X x n)
-- --           (Sq X (RP∞'-fields.notRP∞' X x) n
-- --            , sq-coh X (RP∞'-fields.notRP∞' X x) n)
-- -- comm-field = JRP∞' λ n → SteenrodFunType≡ (RP∞'∙ ℓ-zero) n _ _
-- --   (funExt λ f → cong (subst (EM ℤ/2) (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n)))
-- --           (⌣ₖ-commℤ/2 (n true) (n false) (f true) (f false))
-- --         ∙ help _ (+'-comm (n false) (n true)) _
-- --                  (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n))
-- --                  (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) false n))
-- --            (cp (f false) (f true)))
-- --   where
-- --   help : {n : ℕ} (m : ℕ) (p : n ≡ m) (l : ℕ) (q : m ≡ l) (r : n ≡ l)
-- --     → (x : EM ℤ/2 n)
-- --     → subst (EM ℤ/2) q (subst (EM ℤ/2) p x) ≡ subst (EM ℤ/2) r x
-- --   help = J> (J> λ r x
-- --     → transportRefl _
-- --      ∙ λ j → subst (EM ℤ/2) (isSetℕ _ _ refl r j) x)


-- -- SQ : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → SteenrodFunType X n
-- -- SQ X n = RP∞'→SetRec (isSetSteenrodFunType X n) X
-- --                       (λ x → Sq X x n , sq-coh X x n)
-- --                       (λ x → comm-field X x n)

-- -- STSQ : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
-- --        (f : ((x₁ : fst X) → EM ℤ/2 (n x₁))) → EM ℤ/2 (∑RP∞' X n)
-- -- STSQ X n f = SQ X n .fst f

-- -- SQId : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
-- --   (x : fst X) (g : (x₁ : fst X) → EM ℤ/2 (n x₁))
-- --   → SQ X n .fst g ≡ Sq X x n g
-- -- SQId X n x g i =
-- --   RP∞'→SetRecEq (isSetSteenrodFunType X n) X
-- --                  (λ x → Sq X x n , sq-coh X x n)
-- --                  (λ x → comm-field X x n) x i .fst g

-- -- SQBool : (n : Bool → ℕ) (g : _) → SQ (RP∞'∙ ℓ-zero) n .fst g ≡ cp (g true) (g false)
-- -- SQBool n g = SQId (RP∞'∙ ℓ-zero) n true g ∙ sq≡ n g

-- -- ΣQuadpointTy : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → Type
-- -- ΣQuadpointTy X Y n =
-- --   Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
-- --          → EM ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) ]
-- --       QuadpointedUnordJoin X Y
-- --         (λ x y → EM∙ ℤ/2 (n x y))
-- --         (EM∙ ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) f

-- -- SQ4 : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → ΣQuadpointTy X Y n
-- -- fst (SQ4 X Y n) f = SQ X (λ x → ∑RP∞' Y (n x)) .fst λ x → SQ Y (n x) .fst (f x)
-- -- snd (SQ4 X Y n) g (inlR p) = SQ X (λ x → ∑RP∞' Y (n x)) .snd _ (inlR (fst p , SQ Y (n (fst p)) .snd _ (snd p)))
-- -- snd (SQ4 X Y n) g (inrR f) = SQ X (λ x → ∑RP∞' Y (n x)) .snd _ (inrR λ x → SQ Y (n x) .snd _ (f x))
-- -- snd (SQ4 X Y n) g (pushR p f r i) =
-- --   SQ X (λ x → ∑RP∞' Y (n x)) .snd _
-- --     (pushR (fst p , SQ Y (n (fst p)) .snd _ (snd p))
-- --            (λ x → SQ Y (n x) .snd _ (f x))
-- --            (cong (SQ Y (n (fst p)) .snd (λ x₂ → g (fst p) x₂)) r) i)

-- -- SQ4comm' : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
-- --          → EM ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y)) ]
-- --       QuadpointedUnordJoin Y X
-- --         (λ y x → EM∙ ℤ/2 (n x y))
-- --         (EM∙ ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y))
-- --         (λ g → f (λ x y → g y x))
-- -- fst (SQ4comm' X Y n) f =
-- --   SQ Y (λ z → ∑RP∞' X (λ x → n x z)) .fst
-- --     λ y → SQ X (λ x → n x y) .fst λ x → f x y
-- -- snd (SQ4comm' X Y n) g (inlR x) =
-- --   SQ Y (λ z → ∑RP∞' X (λ x₁ → n x₁ z)) .snd
-- --     (λ y → SQ X (λ x₁ → n x₁ y) .fst (λ x₁ → g y x₁))
-- --       (inlR (fst x , SQ X (λ x₁ → n x₁ (fst x)) .snd (g (fst x)) (snd x)))
-- -- snd (SQ4comm' X Y n) g (inrR f) =
-- --   SQ Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
-- --     (λ y → SQ X (λ x → n x y) .fst (g y))
-- --     (inrR λ y → SQ X (λ x → n x y) .snd (g y) (f y))
-- -- snd (SQ4comm' X Y n) g (pushR a b x i) =
-- --   SQ Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
-- --     (λ y → SQ X (λ x₁ → n x₁ y) .fst (g y))
-- --       (pushR (fst a , SQ X (λ x → n x (fst a)) .snd (g (fst a)) (snd a))
-- --              (λ y → SQ X (λ x → n x y) .snd (g y) (b y))
-- --              (cong (SQ X (λ x₁ → n x₁ (fst a)) .snd (g (fst a))) x) i)

-- -- SQ4comm : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → ΣQuadpointTy X Y n
-- -- fst (SQ4comm X Y n) f =
-- --   subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
-- --     (SQ Y (λ z → ∑RP∞' X (λ x → n x z)) .fst
-- --       λ y → SQ X (λ x → n x y) .fst λ x → f x y)
-- -- snd (SQ4comm X Y n) f p =
-- --     cong (subst (EM ℤ/2) (∑RP∞'Fubini X Y n))
-- --       (SQ4comm' X Y n .snd (λ y x → f x y)
-- --         (UnordJoinFubiniFun X Y _ p))
-- --   ∙ subst-EM∙ (∑RP∞'Fubini X Y n) .snd

-- -- mainA : (A B C D T : Pointed ℓ-zero)
-- --   → Iso (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ]
-- --             JS4 A B C D T f)
-- --          (A →∙ (B →∙ C →∙ D →∙ T ∙ ∙ ∙))
-- -- mainA A B C D T =
-- --   compIso
-- --    (compIso IsMain
-- --      (Σ-cong-iso
-- --        (codomainIso (codomainIso (mainLem C D T)))
-- --        λ f → codomainIsoDep λ a
-- --            → codomainIsoDep λ b
-- --            → codomainIso
-- --              (compIso (congIso {x = f a b} (mainLem C D T))
-- --                (pathToIso (cong (fun (mainLem C D T) (f a b) ≡_)
-- --                  (mainIs .snd)) ))))
-- --     (mainLem A B (C →∙ D →∙ T ∙ ∙))
-- --   where
-- --   T1 = (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ] JS4 A B C D T f)
-- --   T2 = (Σ (fst A → fst B → Σ (fst C → fst D → fst T) (BipointedJoinBool C D T))
-- --                  (BipointedJoinBool A B (Σ (fst C → fst D → fst T) (BipointedJoinBool C D T)
-- --                    , (λ _ _ → snd T) , (λ _ _ _ → refl) )))

-- --   module _ (a : fst A) (b : fst B) (c : fst C) (d : fst D)
-- --            (p : join (a ≡ snd A) (b ≡ snd B))
-- --            (q : join (c ≡ snd C) (d ≡ snd D)) (i j k : I) where
-- --     fill₁ : T1 → fst T
-- --     fill₁ (f , g) =
-- --       hfill (λ k → λ {(i = i0) → g a b c d (push p q k) j
-- --                      ; (i = i1) → snd T
-- --                      ; (j = i0) → g a b c d (inl p) i
-- --                      ; (j = i1) → snd T})
-- --             (inS (g a b c d (inl p) (i ∨ j))) k

-- --     fill₂ : T2 → fst T
-- --     fill₂ (f , g) =
-- --       hfill (λ k → λ {(i = i0) → g a b p j .snd c d q (~ k)
-- --                    ; (i = i1) → f a b .snd c d q (~ k ∨ j)
-- --                    ; (j = i0) → f a b .snd c d q (~ k)
-- --                    ; (j = i1) → snd T})
-- --           (inS (snd T)) k

-- --   T1→T2 : T1 → T2
-- --   fst (fst (T1→T2 (f , p)) a b) c d = f a b c d
-- --   snd (fst (T1→T2 (f , p)) a b) c d t = p a b c d (inr t)
-- --   fst (snd (T1→T2 (f , p)) a b t i) c d = p a b c d (inl t) i
-- --   snd (snd (T1→T2 (f , p)) a b t i) c d q j = fill₁ a b c d t q i j i1 (f , p)

-- --   T2→T1 : T2 → T1
-- --   fst (T2→T1 (f , p)) a b c d = f a b .fst c d
-- --   snd (T2→T1 (f , p)) a b c d (inl x) i = p a b x i .fst c d
-- --   snd (T2→T1 (f , p)) a b c d (inr x) = f a b .snd c d x
-- --   snd (T2→T1 (f , g)) a b c d (push p q i) j = fill₂ a b c d p q i j i1 (f , g)

-- --   IsMain : Iso T1 T2
-- --   Iso.fun IsMain = T1→T2
-- --   Iso.inv IsMain = T2→T1
-- --   fst (Iso.rightInv IsMain (f , p) i) = fst (T1→T2 (T2→T1 (f , p)))
-- --   fst (snd (Iso.rightInv IsMain (f , p) i) a b t j) = p a b t j .fst
-- --   snd (snd (Iso.rightInv IsMain (f , g) i) a b p j) c d q k =
-- --     hcomp (λ r → λ {(i = i0) → fill₁ a b c d p q j k r ((λ a b c d → f a b .fst c d) , (snd (T2→T1 (f , g))))
-- --                    ; (i = i1) → snd (g a b p j) c d q k
-- --                    ; (j = i0) → sd r i k
-- --                    ; (j = i1) → snd T
-- --                    ; (k = i0) → g a b p j .fst c d
-- --                    ; (k = i1) → snd T})
-- --            (cb k j i)
-- --     where
-- --     sq : (k i r : I) → fst T
-- --     sq k i r =
-- --       hfill (λ r → λ {(i = i0) → g a b p k .snd c d q (~ r)
-- --                      ; (i = i1) → f a b .snd c d q (~ r ∨ k)
-- --                      ; (k = i0) → f a b .snd c d q (~ r)
-- --                      ; (k = i1) → snd T})
-- --             (inS (snd T))
-- --             r

-- --     sd : Cube (λ i j → sq j i i1)
-- --                (λ i k → f a b .snd c d q k)
-- --                (λ r k → fill₂ a b c d p q r k i1
-- --                           (f , λ a b p → g a b p))
-- --                (λ r k → snd (f a b) c d q k)
-- --                (λ r i → f a b .fst c d) (λ _ _ → pt T)
-- --     sd r i k =
-- --       hcomp (λ w → λ {(r = i0) → sq k i w
-- --                      ; (r = i1) → f a b .snd c d q (~ w ∨ k)
-- --                      ; (i = i0) → fill₂ a b c d p q r k w (f , λ a b p → g a b p)
-- --                      ; (i = i1) → f a b .snd c d q (~ w ∨ k)
-- --                      ; (k = i0) → f a b .snd c d q (~ w)
-- --                      ; (k = i1) → snd T})
-- --                 (snd T)

-- --     cb : Cube (λ j i → g a b p j .fst c d) (λ _ _ → pt T)
-- --               (λ i j → sq i j i1) (λ _ _ → pt T)
-- --               (λ k j → g a b p (j ∨ k) .fst c d)
-- --               λ k j → snd (g a b p j) c d q k
-- --     cb k j i =
-- --       hcomp (λ r → λ {(i = i0) → g a b p (k ∨ j) .snd c d q (~ r)
-- --                      ; (i = i1) → snd (g a b p j) c d q (~ r ∨ k)
-- --                      ; (j = i1) → snd T
-- --                      ; (k = i0) → g a b p j .snd c d q (~ r)
-- --                      ; (k = i1) → snd T})
-- --             (snd T)
-- --   fst (Iso.leftInv IsMain (f , g) i) = f
-- --   snd (Iso.leftInv IsMain (f , g) i) a b c d (inl p) = g a b c d (inl p)
-- --   snd (Iso.leftInv IsMain (f , g) i) a b c d (inr p) = g a b c d (inr p)
-- --   snd (Iso.leftInv IsMain (f , g) i) a b c d (push p q j) k =
-- --     hcomp (λ r → λ {(i = i0) → fill₂ a b c d p q j k r
-- --                                    (fst (T1→T2 (f , g)) , snd (T1→T2 (f , g)))
-- --                    ; (i = i1) → ss r j k
-- --                    ; (j = i0) → s2 r k i
-- --                    ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
-- --                    ; (k = i0) → g a b c d (inr q) (~ r)
-- --                    ; (k = i1) → pt T})
-- --            (snd T)
-- --     where
-- --     PP : (i j k : I) → fst T
-- --     PP i j k = doubleWhiskFiller {A = λ i → g a b c d (inr q) (~ i) ≡ pt T} refl
-- --           (λ i j → g a b c d (inr q) (~ i ∨ j))
-- --           (λ j k → g a b c d (push p q (~ j)) k)
-- --           k i j

-- --     s2 : Cube (λ _ _ → pt T) (λ k i → g a b c d (inl p) k)
-- --               (λ r i → g a b c d (inr q) (~ r)) (λ _ _ → pt T)
-- --               (λ r k → fill₁ a b c d p q k (~ r) i1 (f , g))
-- --               λ r k → PP r k i1
-- --     s2 r k i =
-- --       hcomp (λ j → λ {(r = i0) → pt T
-- --                      ; (r = i1) → g a b c d (push p q (~ j ∧ i)) k
-- --                      ; (k = i0) → g a b c d (push p q (j ∨ i)) (~ r)
-- --                      ; (k = i1) → pt T
-- --                      ; (i = i0) → fill₁ a b c d p q k (~ r) j (f , g)
-- --                      ; (i = i1) → PP r k j})
-- --             (g a b c d (push p q i) (k ∨ ~ r))

-- --     ss : Cube (λ _ _ → pt T) (λ j k → g a b c d (push p q j) k)
-- --                (λ i j → PP i j i1)
-- --                (λ r k → g a b c d (inr q) (~ r ∨ k))
-- --                (λ r j → g a b c d (inr q) (~ r))
-- --                (λ r j → pt T)
-- --     ss r j k =
-- --       hcomp (λ w → λ {(r = i0) → pt T
-- --                    ; (r = i1) → g a b c d (push p q (~ w ∨ j)) k
-- --                    ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
-- --                    ; (k = i0) → g a b c d (inr q) (~ r)
-- --                    ; (k = i1) → pt T})
-- --            (g a b c d (inr q) (~ r ∨ k))

-- --   mainIs :  (isoToPath (mainLem C D T) i0 , (λ c d → pt T) , λ _ _ _ → refl)
-- --           ≃∙ (C →∙ (D →∙ T ∙) ∙)
-- --   fst mainIs = isoToEquiv (mainLem C D T)
-- --   snd mainIs = cong (Iso.fun SmashAdjIso)
-- --        (ΣPathP ((funExt (
-- --          λ { (inl x) → refl
-- --             ; (inr x) → refl
-- --             ; (push (inl x) i) → refl
-- --             ; (push (inr x) i) → refl
-- --             ; (push (push a i₁) i) → refl})) , refl))
-- --             ∙ SmashAdj≃∙ .snd
-- -- {-
-- --      ((isoToEquiv (mainLem C D T)))
-- --      (cong (Iso.fun SmashAdjIso)
-- --        (ΣPathP ((funExt (
-- --          λ { (inl x) → refl
-- --             ; (inr x) → refl
-- --             ; (push (inl x) i) → refl
-- --             ; (push (inr x) i) → refl
-- --             ; (push (push a i₁) i) → refl})) , refl))
-- --             ∙ SmashAdj≃∙ .snd)
-- -- -}

-- -- ΣQuadpointTyBool : (n : Bool → Bool → ℕ)
-- --   → Iso (ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
-- --         (EM∙ ℤ/2 (n true true)
-- --      →∙ (EM∙ ℤ/2 (n true false)
-- --      →∙ EM∙ ℤ/2 (n false true)
-- --      →∙ EM∙ ℤ/2 (n false false)
-- --      →∙ EM∙ ℤ/2 ((n true true +' n true false)
-- --                +' (n false true +' n false false)) ∙ ∙ ∙))
-- -- ΣQuadpointTyBool n =
-- --    (compIso
-- --     (Σ-cong-iso
-- --      (invIso (compIso (invIso curryIso)
-- --      (compIso (invIso curryIso)
-- --      (compIso (invIso curryIso)
-- --      (domIso (invIso help))))))
-- --       λ f → invIso (compIso
-- --         (compIso (invIso curryIso)
-- --           (compIso (invIso curryIso)
-- --             (compIso (invIso curryIso)
-- --               (invIso
-- --                 (ΠIso idIso
-- --                   λ {(((x , y) , z) , w)
-- --                → domIso (compIso join-UnordJoinR-iso
-- --                    (Iso→joinIso
-- --                      join-UnordJoinR-iso
-- --                      join-UnordJoinR-iso))})))))
-- --           (ΠIso (invIso help) λ _ → idIso)))
-- --     (mainA (EM∙ ℤ/2 (n true true))
-- --            (EM∙ ℤ/2 (n true false))
-- --            (EM∙ ℤ/2 (n false true))
-- --            (EM∙ ℤ/2 (n false false))
-- --      (EM∙ ℤ/2 ((n true true +' n true false)
-- --            +' (n false true +' n false false)))))
-- --   where
-- --   help : Iso ((x y : fst (RP∞'∙ ℓ-zero)) → EM∙ ℤ/2 (n x y) .fst)
-- --              (((EM ℤ/2 (n true true)
-- --               × EM ℤ/2 (n true false))
-- --               × EM ℤ/2 (n false true))
-- --               × EM ℤ/2 (n false false))
-- --   help = compIso (compIso ΠBool×Iso
-- --                   (prodIso ΠBool×Iso ΠBool×Iso))
-- --                   (invIso Σ-assoc-Iso)

-- -- {-
-- -- ΣQuadpointTyPres : (n : Bool → Bool → ℕ)
-- --   (f : ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
-- --   → Path (EM ℤ/2 (n true true) →
-- --       (EM ℤ/2 (n true false) →
-- --        EM ℤ/2 (n false true) →
-- --        EM ℤ/2 (n false false) →
-- --        EM ℤ/2
-- --          ((n true true +' n true false)
-- --        +' (n false true +' n false false))))
-- --         (λ x y z w → Iso.fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z .fst w)
-- --         λ x y z w → f .fst (CasesBool true
-- --                              (CasesBool true x y)
-- --                              (CasesBool true z w))
-- -- ΣQuadpointTyPres n f = refl
-- -- -}

-- -- isSetΣQuadPoint : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → isSet (ΣQuadpointTy X Y n)
-- -- isSetΣQuadPoint =
-- --   RP∞'pt→Prop (λ Y → isPropΠ2 (λ _ _ → isPropIsSet))
-- --     (RP∞'pt→Prop (λ Y → isPropΠ (λ _ → isPropIsSet))
-- --       λ n → isOfHLevelRetractFromIso 2
-- --               (ΣQuadpointTyBool n)
-- --               (isConnected→∙ (suc (n true true)) 1
-- --                 (isConnectedEM (n true true))
-- --                 (isConnected→∙ (suc (n true false)) (n true true + 1)
-- --                   (isConnectedEM (n true false))
-- --                   (isConnected→∙ (suc (n false true))
-- --                     ((n true false) + (n true true + 1))
-- --                     (isConnectedEM (n false true))
-- --                     (isConnected→∙
-- --                       (suc (n false false))
-- --                       (n false true + (n true false + (n true true + 1)))
-- --                       (isConnectedEM (n false false))
-- --                       (subst (λ k → isOfHLevel (suc k) (EM ℤ/2 (N' n)))
-- --                         (lem n)
-- --                         (hLevelEM ℤ/2 (N' n))))))))
-- --   where
-- --   N' : (n : Bool → Bool → ℕ) → ℕ
-- --   N' n = ((n true true +' n true false) +' (n false true +' n false false))

-- --   lem : (n : _) → suc (N' n)
-- --                  ≡ (n false false + (n false true + (n true false + (n true true + 1))))
-- --   lem n =  cong suc ((cong₂ _+'_ (+'≡+ (n true true) (n true false))
-- --                                 (+'≡+ (n false true) (n false false))
-- --                  ∙ +'≡+ _ _)
-- --                  ∙ +-assoc (n true true + n true false ) (n false true) (n false false))
-- --          ∙ cong (_+ n false false)
-- --               (cong (_+ n false true)
-- --                 ((λ i → +-comm (+-comm 1 (n true true) i) (n true false) i))
-- --               ∙ +-comm _ (n false true))
-- --          ∙ +-comm _ (n false false)

-- -- ΣQuadPoint≡ : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   (f g : ΣQuadpointTy X Y n)
-- --   → ((t : _) → f .fst t ≡ g .fst t)
-- --   → f ≡ g
-- -- ΣQuadPoint≡ =
-- --   RP∞'pt→Prop (λ X → isPropΠ5 λ Y n _ _ _ → isSetΣQuadPoint X Y n _ _)
-- --     (RP∞'pt→Prop (λ Y → isPropΠ4 λ n _ _ _
-- --                        → isSetΣQuadPoint (RP∞'∙ ℓ-zero) Y n _ _)
-- --      λ n f g p
-- --    → sym (Iso.leftInv (ΣQuadpointTyBool n) f)
-- --    ∙∙ cong (inv (ΣQuadpointTyBool n))
-- --        (main n f g p)
-- --    ∙∙ Iso.leftInv (ΣQuadpointTyBool n) g)
-- --   where
-- --   module _ (n : Bool → Bool → ℕ)
-- --            (f g : ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
-- --          (p : (t : (x y : fst (RP∞'∙ ℓ-zero)) → EM ℤ/2 (n x y))
-- --         →  f .fst t ≡ g .fst t) where
-- --     p' : (x : _) (y : _) (z : _) (w : _)
-- --       → fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z .fst w
-- --       ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y .fst z .fst w
-- --     p' x y z w = p (CasesBool true
-- --                        (CasesBool true x y)
-- --                        (CasesBool true z w))

-- --     module _ {ℓ ℓ' ℓT} {C : Pointed ℓ} {D : Pointed ℓ'} {T : Pointed ℓT}
-- --               (hom : isHomogeneous T) where
-- --       isHomogeneous→∙₂ : isHomogeneous (C →∙ (D →∙ T ∙) ∙)
-- --       isHomogeneous→∙₂ = isHomogeneous→∙ (isHomogeneous→∙ hom)

-- --       module _ {ℓ'' : Level} {B : Pointed ℓ''} where
-- --         isHomogeneous→∙₃ : isHomogeneous (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙)
-- --         isHomogeneous→∙₃ = isHomogeneous→∙ isHomogeneous→∙₂

-- --         isHomogeneous→∙₄ : ∀ {ℓ'''} {A : Pointed ℓ'''}
-- --           → isHomogeneous (A →∙ (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙) ∙)
-- --         isHomogeneous→∙₄ = isHomogeneous→∙ isHomogeneous→∙₃



-- --     T = (n true true +' n true false) +' (n false true +' n false false)

-- --     m4 : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
-- --          (z : EM ℤ/2 (n false true))
-- --        → fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z
-- --        ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y .fst z
-- --     m4 x y z = →∙Homogeneous≡ (isHomogeneousEM T) (funExt (p' x y z))

-- --     m3 : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
-- --        → fun (ΣQuadpointTyBool n) f .fst x .fst y
-- --        ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y
-- --     m3 x y = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM T))
-- --                (funExt (m4 x y))

-- --     m2 : (x : EM ℤ/2 (n true true))
-- --       → fun (ΣQuadpointTyBool n) f .fst x
-- --        ≡ fun (ΣQuadpointTyBool n) g .fst x
-- --     m2 x = →∙Homogeneous≡ (isHomogeneous→∙₂ (isHomogeneousEM T))
-- --              (funExt (m3 x))

-- --     main : fun (ΣQuadpointTyBool n) f ≡ fun (ΣQuadpointTyBool n) g
-- --     main = →∙Homogeneous≡ (isHomogeneous→∙₃ (isHomogeneousEM T))
-- --              (funExt m2)

-- -- SQ4≡SQ4comm : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → SQ4 X Y n ≡ SQ4comm X Y n
-- -- SQ4≡SQ4comm =
-- --   RP∞'pt→Prop (λ _ → isPropΠ2 λ Y n → isSetΣQuadPoint _ Y n _ _)
-- --   (RP∞'pt→Prop (λ Y → isPropΠ λ n → isSetΣQuadPoint _ Y n _ _)
-- --     λ n → ΣQuadPoint≡ _ _ _ _ _
-- --       λ f → SQBool (λ x → ∑RP∞' (RP∞'∙ ℓ-zero) (n x))
-- --                     (λ x → SQ (RP∞'∙ ℓ-zero) (n x) .fst (f x))
-- --            ∙ cong₂ cp (SQBool (n true) (f true))
-- --                       (SQBool (n false) (f false))
-- --            ∙ help (EM ℤ/2) (λ n m x y → cp {n = n} {m = m} x y)
-- --                ⌣ₖ-commℤ/2 assoc⌣ₖ
-- --                (n true true) (n true false)
-- --                (n false true) (n false false)
-- --                (f true true) (f true false)
-- --                (f false true) (f false false)
-- --                (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
-- --            ∙ cong (subst (EM ℤ/2) (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n))
-- --                (sym (SQBool (λ z → ∑RP∞' (RP∞'∙ ℓ-zero) (λ x → n x z))
-- --                          (λ y → SQ (RP∞'∙ ℓ-zero) (λ x → n x y) .fst (λ x → f x y))
-- --                ∙ cong₂ cp (SQBool (λ x → n x true) (λ x → f x true))
-- --                                (SQBool (λ x → n x false) (λ x → f x false)))))
-- --   where
-- --   help : ∀ {ℓ} (A : ℕ → Type ℓ) (compA : (n m : ℕ) (x : A n) (y : A m) → A (n +' m))
-- --     → (⌣comm : (n m : ℕ) (x : A n) (y : A m)
-- --       → compA n m x y
-- --        ≡ subst A (+'-comm m n) (compA m n y x))
-- --     → (⌣assoc : (n m l : ℕ) (x : A n) (y : A m) (z : A l)
-- --       → compA (n +' m) l (compA n m x y) z
-- --        ≡ subst A (+'-assoc n m l)
-- --            (compA n (m +' l) x (compA m l y z)))
-- --     → (n m k l : ℕ) (x : A n) (y : A m) (z : A k) (w : A l)
-- --     → (p : ((n +' k) +' (m +' l)) ≡ ((n +' m) +' (k +' l)))
-- --     → compA (n +' m) (k +' l) (compA n m x y) (compA k l z w)
-- --      ≡ subst A p (compA (n +' k) (m +' l) (compA n k x z) (compA m l y w))
-- --   help A compA ⌣comm ⌣assoc n m k l x y z w p =
-- --       (sym (transportRefl _)
-- --     ∙ (λ i → subst A (isSetℕ _ _ refl (((sym (+'-assoc n m (k +' l))) ∙ p5 ∙ p4) ∙ p) i)
-- --                (compA (n +' m) (k +' l) (compA n m x y) (compA k l z w))))
-- --     ∙ substComposite A ((sym (+'-assoc n m (k +' l)) ∙ p5 ∙ p4)) p _
-- --     ∙ cong (subst A p)
-- --         ((substComposite A (sym (+'-assoc n m (k +' l))) (p5 ∙ p4) _
-- --         ∙ cong (subst A (p5 ∙ p4))
-- --            (cong (subst A (sym (+'-assoc n m (k +' l))))
-- --                  (⌣assoc _ _ _ x y (compA k l z w))
-- --          ∙ subst⁻Subst A (+'-assoc n m (k +' l)) _))
-- --         ∙ substComposite A (cong (_+'_ n) ((p1 ∙ p2) ∙ p3)) p4
-- --            (compA n (m +' (k +' l)) x (compA m (k +' l) y (compA k l z w)))
-- --         ∙ cong (subst A (+'-assoc n k (m +' l)))
-- --           (sym (substLems _ _ ((p1 ∙ p2) ∙ p3) _ .snd
-- --                  x (compA m (k +' l) y (compA k l z w)))
-- --          ∙ cong (compA n (k +' (m +' l)) x)
-- --             (substComposite A (p1 ∙ p2) p3 (compA m (k +' l) y (compA k l z w))
-- --            ∙ cong (subst A p3)
-- --               ((substComposite A p1 p2 (compA m (k +' l) y (compA k l z w))
-- --               ∙ cong (subst A (cong (_+' l) (+'-comm m k)))
-- --                   (sym (⌣assoc m k l y z w)))
-- --               ∙ sym (substLems _ _ (+'-comm m k) _ .fst (compA m k y z) w)
-- --               ∙ cong (λ z → compA (k +' m) l z w)
-- --                  (sym (⌣comm k m z y)))
-- --             ∙ cong (subst A p3)
-- --               (⌣assoc _ _ _ z y w)
-- --            ∙ subst⁻Subst A (+'-assoc k m l) _))
-- --         ∙ sym (⌣assoc _ _ _ x z (compA m l y w)))
-- --     where
-- --     p1 = +'-assoc m k l
-- --     p2 = cong (_+' l) (+'-comm m k)
-- --     p3 = sym (+'-assoc k m l)
-- --     p4 = +'-assoc n k (m +' l)
-- --     p5 = cong (n +'_) ((p1 ∙ p2) ∙ p3)

-- --     substLems : (n n' : ℕ) (p : n ≡ n') (m : ℕ)
-- --       → ((x : A n) (y : A m)
-- --         → compA n' m (subst A p x) y ≡ subst A (cong (_+' m) p) (compA n m x y))
-- --        × ((x : A m) (y : A n)
-- --         → compA m n' x (subst A p y) ≡ subst A (cong (m +'_) p) (compA m n x y))
-- --     substLems n = J> λ m
-- --       → (λ x y → cong (λ x → compA n m x y) (transportRefl x)
-- --                  ∙ sym (transportRefl _))
-- --        , ((λ x y → cong (λ y → compA m n x y) (transportRefl y)
-- --                  ∙ sym (transportRefl _)))

-- -- PreCartan : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
-- --   → (f : (x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
-- --   → STSQ X (λ x → ∑RP∞' Y (n x)) (λ x → STSQ Y (n x) (f x))
-- --    ≡ subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
-- --        (STSQ Y (λ y → ∑RP∞' X (λ x → n x y))
-- --          (λ y → STSQ X (λ x → n x y) (λ x → f x y)))
-- -- PreCartan X Y n f i = SQ4≡SQ4comm X Y n i .fst f

-- -- -- module _ (A B C D :  Pointed ℓ-zero) (T : Pointed ℓ-zero)
-- -- --          (f : A .fst × B .fst × C .fst × D .fst
-- -- --            → fst T) where
-- -- --   BipointedJoinBool : Type
-- -- --   BipointedJoinBool = (a : A .fst) (b : B .fst) (c : C .fst) (d : D .fst)
-- -- --          → join (a ≡ A .snd)
-- -- --              (join (b ≡ B .snd)
-- -- --                (join (c ≡ C .snd)
-- -- --                      (d ≡ D .snd)))
-- -- --          → f (a , b , c , d) ≡ T .snd

-- -- --   BipointedJoinBool* : Type
-- -- --   BipointedJoinBool* = (b : B .fst) (c : C .fst) (d : D .fst)
-- -- --     → Σ[ fr ∈ ((a : A .fst) → join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd))
-- -- --                              → f (a , b , c , d) ≡ T .snd) ]
-- -- --           ((x : singl (A .snd)) →
-- -- --               (Σ[ fl ∈ (f (x .fst , b , c , d) ≡ T .snd) ]
-- -- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- -- --              → fl ≡ fr (x .fst) t)))

-- -- --   BipointedJoinBool** : Type
-- -- --   BipointedJoinBool** = (b : B .fst) (c : C .fst) (d : D .fst)
-- -- --     → Σ[ fr ∈ ((a : A .fst) → join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd))
-- -- --                              → f (a , b , c , d) ≡ T .snd) ]
-- -- --            Σ[ fl ∈ (f (pt A , b , c , d) ≡ T .snd) ]
-- -- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- -- --              → fl ≡ fr (pt A) t)

-- -- --   JS₂ : Type
-- -- --   JS₂ = (c : C .fst) (d : D .fst)
-- -- --     → Σ[ fr ∈ ((a : A .fst) (b : fst B)
-- -- --               → join (c ≡ C .snd) (d ≡ D .snd)
-- -- --               → f (a , b , c , d) ≡ T .snd) ]
-- -- --        Σ[ fl ∈ ((b : fst B) → f (pt A , b , c , d) ≡ T .snd) ]
-- -- --          Σ[ flp ∈ ((b : fst B) → (t : join (c ≡ C .snd) (d ≡ D .snd))
-- -- --                  → fl b ≡ fr (pt A) b t) ]
-- -- --           ((x : singl (B .snd))
-- -- --        → Σ[ frl ∈ ((a : fst A) → f (a , fst x , c , d) ≡ T .snd) ]
-- -- --            Σ[ frp ∈ ((a : fst A) (t : join (c ≡ C .snd) (d ≡ D .snd)) → frl a ≡ fr a (fst x) t) ]
-- -- --              Σ[ r ∈ fl (fst x) ≡ frl (pt A) ]
-- -- --                ((t : join (c ≡ C .snd) (d ≡ D .snd))
-- -- --              → Square r (flp (fst x) t) refl (frp (pt A) t)))

-- -- --   JS₂* : Type
-- -- --   JS₂* = (c : C .fst) (d : D .fst)
-- -- --     → Σ[ fr ∈ ((a : A .fst) (b : fst B)
-- -- --               → join (c ≡ C .snd) (d ≡ D .snd)
-- -- --               → f (a , b , c , d) ≡ T .snd) ]
-- -- --        Σ[ fl ∈ ((b : fst B) → f (pt A , b , c , d) ≡ T .snd) ]
-- -- --          Σ[ flp ∈ ((b : fst B) → (t : join (c ≡ C .snd) (d ≡ D .snd))
-- -- --                  → fl b ≡ fr (pt A) b t) ]
-- -- --           (Σ[ frl ∈ ((a : fst A) → f (a , pt B , c , d) ≡ T .snd) ]
-- -- --            Σ[ frp ∈ ((a : fst A) (t : join (c ≡ C .snd) (d ≡ D .snd)) → frl a ≡ fr a (pt B) t) ]
-- -- --              Σ[ r ∈ fl (pt B) ≡ frl (pt A) ]
-- -- --                ((t : join (c ≡ C .snd) (d ≡ D .snd))
-- -- --              → Square r (flp (pt B) t) refl (frp (pt A) t)))

-- -- --   module _ (fl₁ : ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd))
-- -- --                 (fl₂ : ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd))
-- -- --                 (fl₁₂ : (c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d)
-- -- --                 where
-- -- --     TL : singl (snd C) → Type
-- -- --     TL (c , p) =
-- -- --       Σ[ fr ∈ ((a : fst A) (b : fst B) (d : fst D) → f (a , b , c , d) ≡ T .snd) ]
-- -- --         Σ[ flp ∈ ((b : fst B) (d : fst D)  → fl₁ b c d ≡ fr (pt A) b d) ]
-- -- --           Σ[ frp ∈ ((a : fst A) (d : fst D) → fl₂ a c d ≡ fr a (pt B) d) ]
-- -- --             ((d : fst D) → Square (fl₁₂ c d) (flp (pt B) d) refl (frp (pt A) d))
-- -- --     TR : singl (snd D) → Type
-- -- --     TR (d , p) =
-- -- --       Σ[ fr ∈ ((a : fst A) (b : fst B) (c : fst C) → f (a , b , c , d) ≡ T .snd) ]
-- -- --         Σ[ flp ∈ ((b : fst B) (c : fst C)  → fl₁ b c d ≡ fr (pt A) b c) ]
-- -- --           Σ[ frp ∈ ((a : fst A) (c : fst C) → fl₂ a c d ≡ fr a (pt B) c) ]
-- -- --             ((c : fst C) → Square (fl₁₂ c d) (flp (pt B) c) refl (frp (pt A) c))

-- -- --     TLR : (c : singl (snd C)) (d : singl (snd D)) → TL c → TR d → Type
-- -- --     TLR (c , p) (d , q) (frₗ , flpₗ , frpₗ , sqₗ) (frᵣ , flpᵣ , frpᵣ , sqᵣ) =
-- -- --       Σ[ frₗᵣ ∈ (((a : fst A) (b : fst B) → frₗ a b d ≡ frᵣ a b c)) ]
-- -- --       Σ[ flpₗᵣ ∈ ((b : fst B) → PathP (λ i → fl₁ b c d ≡ frₗᵣ (pt A) b i) (flpₗ b d) (flpᵣ b c)) ]
-- -- --       Σ[ frpₗᵣ ∈ ((a : fst A) → PathP (λ i → fl₂ a c d ≡ frₗᵣ a (pt B) i) (frpₗ a d) (frpᵣ a c)) ]
-- -- --         Cube (sqₗ d) (sqᵣ c)
-- -- --              (λ i j → fl₁₂ c d j) (flpₗᵣ (pt B))
-- -- --              (λ j i → fl₁ (pt B) c d) (frpₗᵣ (pt A))


-- -- --   JS₃* : Type
-- -- --   JS₃* = Σ[ fl₁ ∈ ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd) ]
-- -- --            Σ[ fl₂ ∈ ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd) ]
-- -- --             Σ[ fl₁₂ ∈ ((c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d) ]
-- -- --              Σ[ l ∈ ((c : _) → TL fl₁ fl₂ fl₁₂ c) ]
-- -- --               Σ[ r ∈ ((c : _) → TR fl₁ fl₂ fl₁₂ c) ]
-- -- --                 ((c : singl (snd C)) (d : singl (snd D)) → TLR fl₁ fl₂ fl₁₂ c d (l c) (r d))

-- -- --   JS₃** : Type
-- -- --   JS₃** = Σ[ fl₁ ∈ ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd) ]
-- -- --            Σ[ fl₂ ∈ ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd) ]
-- -- --             Σ[ fl₁₂ ∈ ((c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d) ]
-- -- --              Σ[ l ∈ (TL fl₁ fl₂ fl₁₂ (pt C , refl)) ]
-- -- --               Σ[ r ∈ (TR fl₁ fl₂ fl₁₂ (pt D , refl)) ]
-- -- --                 (TLR fl₁ fl₂ fl₁₂ (pt C , refl) (pt D , refl) l r)

-- -- --   module _ (js : JS₃**) where
-- -- --     open import Cubical.HITs.SmashProduct
-- -- --     JS₃**→' : (A ⋀∙ (B ⋀∙ (C ⋀∙ D))) →∙ T
-- -- --     fst JS₃**→' (inl x) = pt T
-- -- --     fst JS₃**→' (inr (a , inl x)) = {!f (a , ?)!} -- pt T
-- -- --     fst JS₃**→' (inr (a , inr (b , inl x))) = {!!} -- pt T
-- -- --     fst JS₃**→' (inr (a , inr (b , inr (c , d)))) = f (a , b , c , d)
-- -- --     fst JS₃**→' (inr (a , inr (b , push (inl x) i))) = snd js .snd .snd .snd .fst .fst a b x (~ i)
-- -- --     fst JS₃**→' (inr (a , inr (b , push (inr x) i))) = snd js .snd .snd .fst .fst a b x (~ i)
-- -- --     fst JS₃**→' (inr (a , inr (b , push (push tt i₁) i))) = snd js .snd .snd .snd .snd .fst a b (~ i₁) (~ i)
-- -- --     fst JS₃**→' (inr (a , push (inl x) i)) = {!f (a , pt B , pt C , ?)!} -- pt T
-- -- --     fst JS₃**→' (inr (a , push (inr (inl x)) i)) = {!f (a , pt B , pt C , x)!} -- snd T
-- -- --     fst JS₃**→' (inr (a , push (inr (inr (c , d))) i)) = snd js .fst a c d (~ i)
-- -- --     fst JS₃**→' (inr (a , push (inr (push (inl x) i₁)) i)) = {!!}
-- -- --     fst JS₃**→' (inr (a , push (inr (push (inr x) i₁)) i)) = {!snd js .snd .snd .fst .snd .snd .fst a x (~ i₁) (~ i)!}
-- -- --     fst JS₃**→' (inr (a , push (inr (push (push a₁ i₂) i₁)) i)) = {!!}
-- -- --     fst JS₃**→' (inr (a , push (push a₁ i₁) i)) = {!!}
-- -- --     fst JS₃**→' (push a i) = {!!}
-- -- --     snd JS₃**→' = {!!}

-- -- --     JS₃**→ : A →∙ (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙)
-- -- --     fst (fst (fst (fst JS₃**→ a) b) c) d = f (a , b , c , d)
-- -- --     snd (fst (fst (fst JS₃**→ a) b) c) = snd js .snd .snd .snd .fst .fst a b c
-- -- --     fst (snd (fst (fst JS₃**→ a) b) i) d = snd js .snd .snd .fst .fst a b d i
-- -- --     snd (snd (fst (fst JS₃**→ a) b) i) = {!snd js .snd .snd .snd .snd .fst a b  i!}
-- -- --     fst (fst (snd (fst JS₃**→ a) i) c) d = snd js .fst a c d i
-- -- --     snd (fst (snd (fst JS₃**→ a) i) c) j = {!!}
-- -- --     fst (snd (snd (fst JS₃**→ a) i) j) d = {!!}
-- -- --     snd (snd (snd (fst JS₃**→ a) i) j) k = {!!}
-- -- --     fst (fst (fst (snd JS₃**→ i) b) c) d = fst js b c d i
-- -- --     snd (fst (fst (snd JS₃**→ i) b) c) j = {!!}
-- -- --     fst (snd (fst (snd JS₃**→ i) b) j) d = {!!}
-- -- --     snd (snd (fst (snd JS₃**→ i) b) j) k = {!!}
-- -- --     fst (fst (snd (snd JS₃**→ i) j) c) d = {!!}
-- -- --     snd (fst (snd (snd JS₃**→ i) j) c) k = {!!}
-- -- --     snd (snd (snd JS₃**→ i) j) = {!!}

-- -- --   Iso-JS₃*-JS₃** : Iso JS₃* JS₃**
-- -- --   Iso-JS₃*-JS₃** =
-- -- --     Σ-cong-iso-snd λ f' → Σ-cong-iso-snd λ g → Σ-cong-iso-snd λ fg
-- -- --       → compIso (Σ-cong-iso-snd (λ r → Σ-cong-iso-snd λ s
-- -- --         → compIso (DomainContrIso (isContrSingl (snd C)))
-- -- --                    (DomainContrIso (isContrSingl (snd D)))))
-- -- --            (compIso (ΣDomainContrIso {C = λ c l → Σ ((d : _) → TR f' g fg d)
-- -- --                      λ r → TLR f' g fg c (pt D , refl) l (r (pt D , refl))} (isContrSingl (snd C)))
-- -- --              (Σ-cong-iso-snd λ l →
-- -- --                ΣDomainContrIso {C = λ d r → TLR f' g fg (pt C , refl) d l r} (isContrSingl (snd D))))

-- -- --   Iso₂ : Iso BipointedJoinBool** JS₂
-- -- --   fst (Iso.fun Iso₂ F c d) a b t = F b c d .fst a (inr t)
-- -- --   fst (snd (Iso.fun Iso₂ F c d)) b = F b c d .snd .fst
-- -- --   fst (snd (snd (Iso.fun Iso₂ F c d))) b t = F b c d .snd .snd (inr t)
-- -- --   fst (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)) a =
-- -- --     F b c d .fst a (inl (sym p))
-- -- --   fst (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p))) a t =
-- -- --     cong (F b c d .fst a) (push (sym p) t)
-- -- --   fst (snd (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)))) =
-- -- --     F b c d .snd .snd (inl (sym p))
-- -- --   snd (snd (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)))) t =
-- -- --     cong (F b c d .snd .snd) (push (sym p) t)
-- -- --   fst (Iso.inv Iso₂ F b c d) a (inl x) = F c d .snd .snd .snd (b , sym x) .fst a
-- -- --   fst (Iso.inv Iso₂ F b c d) a (inr t) = F c d .fst a b t
-- -- --   fst (Iso.inv Iso₂ F b c d) a (push x t i) =
-- -- --     F c d .snd .snd .snd (b , sym x) .snd .fst a t i
-- -- --   fst (snd (Iso.inv Iso₂ F b c d)) = F c d .snd .fst b
-- -- --   snd (snd (Iso.inv Iso₂ F b c d)) (inl x) =
-- -- --     F c d .snd .snd .snd (b , sym x) .snd .snd .fst
-- -- --   snd (snd (Iso.inv Iso₂ F b c d)) (inr t) = F c d .snd .snd .fst b t
-- -- --   snd (snd (Iso.inv Iso₂ F b c d)) (push a t i) =
-- -- --     F c d .snd .snd .snd (b , sym a) .snd .snd .snd t i
-- -- --   Iso.rightInv Iso₂ = λ _ → refl
-- -- --   Iso.leftInv Iso₂ F = funExt λ b → funExt λ c → funExt λ x →
-- -- --     ΣPathP (funExt (λ a → funExt λ { (inl x) → refl
-- -- --                                     ; (inr x) → refl
-- -- --                                     ; (push a x i) → refl})
-- -- --            , ΣPathP (refl , (funExt (λ { (inl x) → refl
-- -- --                            ; (inr x) → refl
-- -- --                            ; (push a x i) → refl}))))

-- -- --   Iso₂* : Iso BipointedJoinBool** JS₂*
-- -- --   Iso₂* =
-- -- --     compIso Iso₂
-- -- --       (codomainIsoDep λ c → codomainIsoDep λ d →
-- -- --         Σ-cong-iso-snd λ f → Σ-cong-iso-snd λ g → Σ-cong-iso-snd
-- -- --         λ h → DomainContrIso (isContrSingl (B .snd)))

-- -- --   Iso₃ : Iso JS₂* JS₃*
-- -- --   fst (Iso.fun Iso₃ F) b c d = F c d .snd .fst b
-- -- --   fst (snd (Iso.fun Iso₃ F)) a c d = F c d .snd .snd .snd .fst a
-- -- --   fst (snd (snd (Iso.fun Iso₃ F))) c d = F c d .snd .snd .snd .snd .snd .fst
-- -- --   fst (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)) a b d =
-- -- --     F c d .fst a b (inl (sym p))
-- -- --   fst (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p))) b d =
-- -- --     F c d .snd .snd .fst b (inl (sym p))
-- -- --   fst (snd (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)))) a d =
-- -- --     F c d .snd .snd .snd .snd .fst a (inl (sym p))
-- -- --   snd (snd (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)))) d =
-- -- --     F c d .snd .snd .snd .snd .snd .snd (inl (sym p))
-- -- --   fst (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)) a b c =
-- -- --     F c d .fst a b (inr (sym p))
-- -- --   fst (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p))) b c =
-- -- --     F c d .snd .snd .fst b (inr (sym p))
-- -- --   fst (snd (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)))) a c =
-- -- --     F c d .snd .snd .snd .snd .fst a (inr (sym p))
-- -- --   snd (snd (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)))) c =
-- -- --     F c d .snd .snd .snd .snd .snd .snd (inr (sym p))
-- -- --   fst (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)) a b =
-- -- --     cong (F c d .fst a b) (push (sym p) (sym q))
-- -- --   fst (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q))) b i =
-- -- --     F c d .snd .snd .fst b (push (sym p) (sym q) i)
-- -- --   fst (snd (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)))) a i =
-- -- --     F c d .snd .snd .snd .snd .fst a (push (sym p) (sym q) i)
-- -- --   snd (snd (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)))) i =
-- -- --     F c d .snd .snd .snd .snd .snd .snd (push (sym p) (sym q) i)
-- -- --   fst (Iso.inv Iso₃ F c d) a b (inl x) =
-- -- --     F .snd .snd .snd .fst (c , sym x) .fst a b d
-- -- --   fst (Iso.inv Iso₃ F c d) a b (inr x) =
-- -- --     F .snd .snd .snd .snd .fst (d , sym x) .fst a b c
-- -- --   fst (Iso.inv Iso₃ F c d) a b (push p q i) =
-- -- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .fst a b i
-- -- --   fst (snd (Iso.inv Iso₃ F c d)) b = F .fst b c d
-- -- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (inl x) = F .snd .snd .snd .fst (c , sym x) .snd .fst b d
-- -- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (inr x) = F .snd .snd .snd .snd .fst (d , sym x) .snd .fst b c
-- -- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (push p q i) =
-- -- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .fst b i
-- -- --   fst (snd (snd (snd (Iso.inv Iso₃ F c d)))) a = F .snd .fst a c d
-- -- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (inl x) =
-- -- --     F .snd .snd .snd .fst (c , sym x) .snd .snd .fst a d
-- -- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (inr x) =
-- -- --     F .snd .snd .snd .snd .fst (d , sym x) .snd .snd .fst a c
-- -- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (push p q i) =
-- -- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .snd .fst a i
-- -- --   fst (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) = F .snd .snd .fst c d
-- -- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (inl x) =
-- -- --     F .snd .snd .snd .fst (c , sym x) .snd .snd .snd d
-- -- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (inr x) =
-- -- --     F .snd .snd .snd .snd .fst (d , sym x) .snd .snd .snd c
-- -- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (push p q i) =
-- -- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .snd .snd i
-- -- --   Iso.rightInv Iso₃ _ = refl
-- -- --   Iso.leftInv Iso₃ F = funExt λ c → funExt λ d →
-- -- --     ΣPathP ((funExt (λ a → funExt λ b → funExt
-- -- --            λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- -- --     , ΣPathP (refl , (ΣPathP ((funExt (λ b
-- -- --       → funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- -- --      , (ΣPathP (refl , (ΣPathP ((funExt (λ a →
-- -- --         funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- -- --      , (ΣPathP (refl , (funExt (λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))))))))))))


-- -- --            Σ[ fl ∈ (f (pt A , b , c , d) ≡ T .snd) ]
-- -- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- -- --              → fl ≡ fr (pt A) t)

-- -- --   Iso₁ : Iso BipointedJoinBool BipointedJoinBool*
-- -- --   fst (Iso.fun Iso₁ F b c d) a x = F a b c d (inr x)
-- -- --   fst (snd (Iso.fun Iso₁ F b c d) (a , p)) = F a b c d (inl (sym p))
-- -- --   snd (snd (Iso.fun Iso₁ F b c d) (a , p)) t = cong (F a b c d) (push (sym p) t)
-- -- --   Iso.inv Iso₁ F a b c d (inl x) = F b c d .snd (a , sym x) .fst
-- -- --   Iso.inv Iso₁ F a b c d (inr t) = F b c d .fst a t
-- -- --   Iso.inv Iso₁ F a b c d (push p t i) = F b c d .snd (a , sym p) .snd t i
-- -- --   Iso.rightInv Iso₁ = λ _ → refl
-- -- --   Iso.leftInv Iso₁ F = funExt λ a → funExt λ b → funExt λ c → funExt λ d
-- -- --     → funExt λ { (inl x) → refl ; (inr x) → refl ; (push a x i) → refl}

-- -- --   Iso₁' : Iso BipointedJoinBool BipointedJoinBool**
-- -- --   Iso₁' = compIso Iso₁ (codomainIsoDep λ b → codomainIsoDep λ c → codomainIsoDep λ d
-- -- --     → Σ-cong-iso-snd λ f → DomainContrIso (isContrSingl (A .snd)))

-- -- -- JoinStructureBool* : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- -- --   (f : A true true .fst × A true false .fst
-- -- --      × A false true .fst × A false false .fst
-- -- --     → fst B)
-- -- --   → Type
-- -- -- JoinStructureBool* A B f =
-- -- --   (g : A true true .fst × A true false .fst
-- -- --      × A false true .fst × A false false .fst)
-- -- --   → join (fst g ≡ A true true .snd)
-- -- --       (join (snd g .fst ≡ A true false .snd)
-- -- --         (join (snd (snd g) .fst ≡ A false true .snd)
-- -- --               (snd (snd g) .snd ≡ A false false .snd)))
-- -- --   → f g ≡ B .snd

-- -- -- 4→∙ : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero) → Type ℓ-zero
-- -- -- 4→∙ A B = A true true →∙ (A true false →∙ (A false true →∙ (A false false →∙ B ∙) ∙) ∙)

-- -- -- 4→∙' : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- -- --       → Type ℓ-zero
-- -- -- 4→∙' A B =
-- -- --   Σ[ f ∈ (A true true .fst → A true false .fst
-- -- --        → A false true .fst → A false false .fst → fst B) ]
-- -- --    Σ[ f-inl-inl ∈ ((a : singl (A true true .snd)) (b : _) (c : _) (d : _) → f (fst a) b c d ≡ pt B) ]
-- -- --     Σ[ f-inl-inr ∈ ((b : singl (A true false .snd)) (a : _) (c : _) (d : _) → f a (fst b) c d ≡ pt B) ]
-- -- --      Σ[ f-inl-push ∈ (((a : singl (A true true .snd)) (b : singl (A true false .snd)) (c : _) (d : _)
-- -- --                      → f-inl-inl a (fst b) c d ≡ f-inl-inr b (fst a) c d)) ]
-- -- --     Σ[ f-inr-inl ∈ ((c : singl (A false true .snd)) (a : _) (b : _)  (d : _) → f a b (fst c) d ≡ pt B) ]
-- -- --      Σ[ f-inr-inr ∈ ((d : singl (A false false .snd)) (a : _) (b : _) (c : _) → f a b c (fst d) ≡ pt B) ]
-- -- --        Σ[ f-inl-push ∈ ((c : singl (A false true .snd)) (d : singl (A false false .snd)) (a : _) (b : _)
-- -- --          → f-inr-inl c a b (fst d) ≡ f-inr-inr d a b (fst c)) ]
-- -- --        {!Σ[ f-inl-push ∈ ((c : singl (A false true .snd)) (d : singl (A false false .snd)) (a : _) (b : _)
-- -- --          → f-inr-inl c a b (fst d) ≡ f-inr-inr d a b (fst c)) ]!}

-- -- -- pss : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero) (f : _) → JoinStructureBool A B f
-- -- -- pss A B f (x , y , z , w) (inl (inl p)) = {!p!}
-- -- -- pss A B f (x , y , z , w) (inl (inr q)) = {!q!}
-- -- -- pss A B f (x , y , z , w) (inl (push p q i)) = {!!}
-- -- -- pss A B f (x , y , z , w) (inr (inl p)) = {!!}
-- -- -- pss A B f (x , y , z , w) (inr (inr q)) = {!!}
-- -- -- pss A B f (x , y , z , w) (inr (push p q i)) = {!!}
-- -- -- pss A B f (x , y , z , w) (push (inl p) (inl q) i) = {!!}
-- -- -- pss A B f (x , y , z , w) (push (inr p) (inl q) i) = {!!}
-- -- -- pss A B f (x , y , z , w) (push (push p q i₁) (inl r) i) = {!!}
-- -- -- pss A B f (x , y , z , w) (push p (inr q) i) = {!!}
-- -- -- pss A B f (x , y , z , w) (push p (push q r i₁) i) = {!!}


-- -- -- JoinStructureBoolD : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- -- --   → Σ _ (JoinStructureBool A B)
-- -- --   → A true true →∙ (A true false →∙ (A false true →∙ (A false false →∙ B ∙) ∙) ∙)
-- -- -- fst (fst (fst (fst (JoinStructureBoolD A B (f , p)) x) y) z) w =
-- -- --   f (x , y , z , w)
-- -- -- snd (fst (fst (fst (JoinStructureBoolD A B (f , p)) x) y) z) =
-- -- --   p (x , y , z , snd (A false false)) (inr (inr refl))
-- -- -- fst (snd (fst (fst (JoinStructureBoolD A B (f , p)) x) y) i) w =
-- -- --   p (x , y , snd (A false true) , w) (inr (inl refl)) i
-- -- -- snd (snd (fst (fst (JoinStructureBoolD A B (f , p)) x) y) i) = {!!}
-- -- -- fst (fst (snd (fst (JoinStructureBoolD A B (f , p)) x) i) z) w =
-- -- --   p (x , snd (A true false) , z , w) (inl (inr refl)) i
-- -- -- snd (fst (snd (fst (JoinStructureBoolD A B (f , p)) x) i) z) = {!!}
-- -- -- fst (snd (snd (fst (JoinStructureBoolD A B (f , p)) x) i) j) w = {!!}
-- -- -- snd (snd (snd (fst (JoinStructureBoolD A B (f , p)) x) i) j) = {!!}
-- -- -- fst (fst (fst (snd (JoinStructureBoolD A B (f , p)) i) y) z) w =
-- -- --   p (snd (A true true) , y , z , w) (inl (inl refl)) i
-- -- -- snd (fst (fst (snd (JoinStructureBoolD A B (f , p)) i) y) z) j = {!!}
-- -- -- snd (fst (snd (JoinStructureBoolD A B (f , p)) i) y) = {!!}
-- -- -- snd (snd (JoinStructureBoolD A B (f , p)) i) = {!!}

-- -- -- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Type ℓ) where

-- -- --   JoinStructure : ((f : (x : fst X) (y : fst Y) → A x y .fst) → B) → Type ℓ
-- -- --   JoinStructure f =
-- -- --        (g : (x : fst X) (y : fst Y) → A x y .fst)
-- -- --     → UnordJoinR² X Y (λ x y → g x y ≡ pt (A x y))
-- -- --     → f g ≡ f (λ x y → pt (A x y))

-- -- -- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Type ℓ) where

-- -- --   JoinStructure→ : (t : (f : (x : fst X) (y : fst Y) → A x y .fst) → B)
-- -- --     → JoinStructure X Y A B t
-- -- --     → JoinStructure Y X (λ y x → A x y) B
-- -- --                     λ f → t λ x y → f y x
-- -- --   JoinStructure→ f st g pr =
-- -- --     st (λ x y → g y x)
-- -- --        (UnordJoinFubiniFun Y X (λ x y → g x y ≡ pt (A y x)) pr)


-- -- --   inr* : _ → UnordSmash∙² X Y A .fst
-- -- --   inr* = inr

-- -- --   inr-case : (g : (x₁ : fst X) (y : fst Y) → A x₁ y .fst) (x : fst X)
-- -- --     → UnordJoinR Y (λ y → g x y ≡ pt (A x y))
-- -- --     → Path (UnordSmash Y (A x)) (inr (g x)) (inr (λ y → pt (A x y)))
-- -- --   inr-case g x (inlR (y , z)) = {!z!}
-- -- --   inr-case g x (inrR z) = {!!}
-- -- --   inr-case g x (pushR a b x₁ i) = {!!}

-- -- --   m2 : Σ _ (JoinStructure X Y A B) → UnordSmash∙² X Y A .fst → B
-- -- --   m2 (f , p) (inl x) = {!!}
-- -- --   m2 (f , p) (inr t) = {!!}
-- -- --   m2 (f , p) (push a i) = {!!}

-- -- --   m1 : (f : UnordSmash∙² X Y A .fst → B)
-- -- --      → Σ _ (JoinStructure X Y A B)
-- -- --   fst (m1 f) g = f (inr λ x → inr (g x))
-- -- --   snd (m1 f) g (inlR (x , inlR r)) = {!cong !}
-- -- --   snd (m1 f) g (inlR (x , inrR r)) = {!!}
-- -- --   snd (m1 f) g (inlR (x , pushR a b x₁ i)) = {!!}
-- -- --   snd (m1 f) g (inrR h) = cong f (cong inr* (funExt λ x → inr-case g x (h x)))
-- -- --   snd (m1 f) g (pushR a b x i) = {!!}

-- -- --   -- Smash→ : (Σ[ h ∈ (UnordΠ X (fst ∘ A) → fst B) ]
-- -- --   --              ((f : UnordΠ X ((λ r → fst r) ∘ A))
-- -- --   --              → UnordJoinR X (λ x → f x ≡ pt (A x))
-- -- --   --              → h f ≡ pt B))
-- -- --   --   → (UnordSmash X A → fst B)
-- -- --   -- Smash→ (h , f) (inl x) = pt B
-- -- --   -- Smash→ (h , f) (inr x) = h x
-- -- --   -- Smash→ (h , f) (push (x , a) i) =
-- -- --   --   f (UnordΣ→UnordΠ X A (x , a))
-- -- --   --     (inlR (RP∞'-fields.notRP∞' X x
-- -- --   --     , RP∞'-fields.elimRP∞'β X x a
-- -- --   --       (pt (A (RP∞'-fields.notRP∞' X x))) .snd)) (~ i)
