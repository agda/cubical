{-# OPTIONS --safe --lossy-unification #-}
{-
This module contains 
-}
module Cubical.Homotopy.WhiteheadProducts.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.FinData.Base hiding (suc)
open import Cubical.Data.Vec.Base

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct.SymmetricMonoidal

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Group.Join
open import Cubical.Homotopy.WhiteheadProducts.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Properties

open import Cubical.Tactics.NatSolver.NatExpression renaming (∣ to ∣')
open import Cubical.Tactics.EvenOddSolver

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Properties
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base hiding (·wh)
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Properties
open import Cubical.Homotopy.Group.Join
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat.IsEven
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.S1.Base hiding (_·_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR
open import Cubical.Foundations.Transport
open import Cubical.Homotopy.Connected
open import Cubical.Data.Empty as ⊥

open Iso
open 3x3-span
infixl 7 _·₋₁_

[]comp≡[] : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (f : (S₊∙ (suc n) →∙ X))
       → (g : (S₊∙ (suc m) →∙ X))
       → [ f ∣ g ]comp ≡ [ f ∣ g ]
[]comp≡[] {X = X} {n = n} {m} f g =
  cong (_∘∙ (sphere→Join n m , IsoSphereJoin⁻Pres∙ n m)) (main n m f g)
    where
    ∨fun : {n m : ℕ} (f : (S₊∙ (suc n) →∙ X)) (g : (S₊∙ (suc m) →∙ X))
      → ((_ , inl north) →∙ X)
    ∨fun {n = n} {m} f g =
       ((f ∘∙ (inv (IsoSucSphereSusp n) , IsoSucSphereSusp∙ n)) ∨→
       (g ∘∙ (inv (IsoSucSphereSusp m) , IsoSucSphereSusp∙ m))
       , cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f)

    main : (n m : ℕ) (f : (S₊∙ (suc n) →∙ X)) (g : (S₊∙ (suc m) →∙ X))
      → (∨fun f g ∘∙ (joinTo⋁ {A = S₊∙ n} {B = S₊∙ m} , sym (push tt)))
      ≡ [ f ∣ g ]-pre
    main n m f g =
      ΣPathP ((funExt (λ { (inl x) → rp
                         ; (inr x) → lp
                         ; (push a b i) j → pushcase a b j i}))
          , ((cong₂ _∙_ (symDistr _ _) refl
          ∙ sym (assoc _ _ _)
          ∙ cong (rp ∙_) (rCancel _)
          ∙ sym (rUnit rp))
          ◁ λ i j → rp (i ∨ j)))
      where
      lp = cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f
      rp = cong (fst g) (IsoSucSphereSusp∙ m) ∙ snd g

      help : (n : ℕ) (a : _)
        → Square (cong (inv (IsoSucSphereSusp n)) (σ (S₊∙ n) a)) (σS a)
                  (IsoSucSphereSusp∙ n) (IsoSucSphereSusp∙ n)
      help zero a = cong-∙ SuspBool→S¹ (merid a) (sym (merid (pt (S₊∙ zero))))
                  ∙ sym (rUnit _)
      help (suc n) a = refl

      ∙∙Distr∙ : ∀ {ℓ} {A : Type ℓ} {x y z w u : A}
                 {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} {s : w ≡ u}
               → p ∙∙ q ∙ r ∙∙ s ≡ ((p ∙ q) ∙ r ∙ s)
      ∙∙Distr∙ = doubleCompPath≡compPath _ _ _
               ∙ assoc _ _ _
               ∙ cong₂ _∙_ (assoc _ _ _) refl
               ∙ sym (assoc _ _ _)

      pushcase : (a : S₊ n) (b : S₊ m)
        → Square (cong (∨fun f g .fst
                       ∘ joinTo⋁ {A = S₊∙ n} {B = S₊∙ m}) (push a b))
                  (cong (fst [ f ∣ g ]-pre) (push a b))
                  rp lp
      pushcase a b =
        (cong-∙∙ (∨fun f g .fst) _ _ _
        ∙ (λ i → cong (fst g) (PathP→compPathR∙∙ (help _ b) i)
              ∙∙ symDistr lp (sym rp) i
              ∙∙ cong (fst f) (PathP→compPathR∙∙ (help _ a) i))
        ∙ (λ i → cong (fst g)
                      (IsoSucSphereSusp∙ m
                     ∙∙ σS b
                     ∙∙ (λ j → IsoSucSphereSusp∙ m (~ j ∨ i)))
              ∙∙ compPath-filler' (cong (fst g)
                                        (IsoSucSphereSusp∙ m)) (snd g) (~ i)
               ∙ sym (compPath-filler' (cong (fst f)
                                       (IsoSucSphereSusp∙ n)) (snd f) (~ i))
              ∙∙ cong (fst f)
                      ((λ j → IsoSucSphereSusp∙ n (i ∨ j))
                      ∙∙ σS a
                      ∙∙ sym (IsoSucSphereSusp∙ n))))
       ◁ compPathR→PathP∙∙
           ( ∙∙Distr∙
          ∙ cong₂ _∙_ (cong₂ _∙_ (cong (cong (fst g))
                                       (sym (compPath≡compPath' _ _)))
                                 refl)
                      refl
          ∙ cong₂ _∙_ (cong (_∙ snd g)
                            (cong-∙ (fst g) (IsoSucSphereSusp∙ m) (σS b))
                                     ∙ sym (assoc _ _ _))
                      (cong (sym (snd f) ∙_)
                        (cong-∙ (fst f) (σS a)
                          (sym (IsoSucSphereSusp∙ n)))
                         ∙ assoc _ _ _)
          ∙ sym ∙∙Distr∙
          ∙ cong₃ _∙∙_∙∙_ refl (cong₂ _∙_ refl (compPath≡compPath' _ _)) refl
         ∙ λ i → compPath-filler (cong (fst g) (IsoSucSphereSusp∙ m)) (snd g) i
               ∙∙ ((λ j → snd g (~ j ∧ i)) ∙∙ cong (fst g) (σS b) ∙∙ snd g)
                ∙ (sym (snd f) ∙∙ cong (fst f) (σS a) ∙∙ λ j → snd f (j ∧ i))
               ∙∙ sym (compPath-filler (cong (fst f) (IsoSucSphereSusp∙ n))
                                       (snd f) i))

[_∣_]π*-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
       → [ f ∣ g ]π* ≡ fun (π*SwapIso (suc m) (suc n) X) [ g ∣ f ]π*
[_∣_]π*-comm {n = n} {m = m} =
  ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f g → cong ∣_∣₂
    (WhiteheadProdComm'
        (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
        (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g
    ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f ∘∙_)
       (ΣPathP (refl , sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit _)))))

_·₋₁_ : ℕ → ℕ → ℕ
n ·₋₁ m = suc (suc n · suc m)

[_∣_]π'-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
    → [ f ∣ g ]π'
      ≡ subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
              (-π^ (m ·₋₁ n) [ g ∣ f ]π')
[_∣_]π'-comm {X = X} {n} {m} =
  PT.rec (isPropΠ2 (λ _ _ → squash₂ _ _)) (λ main →
  ST.elim2 (λ _ _ → isSetPathImplicit)
  λ f g → cong ∣_∣₂
    (cong (λ f →
      _∘∙_ {A = S₊∙ (suc (suc (n + suc m)))}
             f (sphere→Join (suc n) (suc m)
              , IsoSphereJoin⁻Pres∙ (suc n) (suc m)))
      (WhiteheadProdComm' (S₊∙ (suc n)) (S₊∙ n)
        (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
        (S₊∙ (suc m)) (S₊∙ m)
        (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g)
      ∙ refl)
   ∙ cong ∣_∣₂ (∘∙-assoc (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f)
                          join-commFun∙
                          (sphere→Join (suc n) (suc m)
                          , (λ _ → inl (ptSn (suc n)))))
   ∙ sym (fromPathP {A = λ i → π' (suc (+-comm (suc m) (suc n) i)) X}
         ((-π^≡iter-Π (suc (suc m · suc n)) [ ∣ g ∣₂ ∣ ∣ f ∣₂ ]π'
         ∙ cong ∣_∣₂ (iter-Π≡∘-S^ (suc (suc m · suc n)) [ g ∣ f ])
         ∙ cong ∣_∣₂ (∘∙-assoc _ _ _))
         ◁ λ i → ∣ [ g ∣ f ]-pre ∘∙ main i ∣₂))) main

  where
  main' : (x : _)
    → PathP (λ i → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
             (-S^ (suc (suc m · suc n)) (join→Sphere (suc n) (suc m) x))
             (join→Sphere (suc m) (suc n) (join-commFun x))
  main' (inl x) i = -S^∙ (suc (suc m · suc n)) .snd i
  main' (inr x) i = -S^∙ (suc (suc m · suc n)) .snd i
  main' (push a b i) j = lem j i
    where
    lem : SquareP (λ i j → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
                  (cong (-S^ (suc (suc m · suc n))) (σS (a ⌣S b)))
                  (sym (σS (b ⌣S a)))
                  (λ i → -S^∙ (suc (suc m · suc n)) .snd i)
                  λ i → -S^∙ (suc (suc m · suc n)) .snd i
    lem = cong (congS (-S^ (suc (suc m · suc n))) ∘ σS)
               (comm⌣S a b)
        ◁ (λ i j → cong-S^σ _ (suc (suc m · suc n))
                     (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
                             i (-S^ (suc (n + m · suc n)) (b ⌣S a))) (~ i) j)
        ▷ (cong σS ((λ i → -S^ (suc (suc m · suc n)) (-S^ ((suc m · suc n)) (b ⌣S a)))
                 ∙ cong invSphere (-S^-comp (suc m · suc n) (suc m · suc n) (b ⌣S a)
                                 ∙ -S^·2 (suc m · suc n) (b ⌣S a)))
             ∙ σ-invSphere _ (b ⌣S a))


  main : ∥ PathP (λ i → S₊∙ (suc (+-comm (suc m) (suc n) i))
                      →∙ join∙ (S₊∙ (suc m)) (S₊∙ (suc n)))
                 ((sphere→Join (suc m) (suc n) , refl)
                 ∘∙ -S^∙ (suc (suc m · suc n)))
                 (join-commFun∙ ∘∙ (sphere→Join (suc n) (suc m) , refl)) ∥₁
  main = TR.rec (isProp→isOfHLevelSuc (m + suc n) squash₁)
    (λ Q → ∣ ΣPathP (fstEq , Q) ∣₁)
    (isConnectedPathP _
      (isConnectedPath _
        (subst (isConnected (suc (suc (suc (m + suc n)))))
          (isoToPath (invIso (joinSphereIso' (suc m) (suc n))))
          (sphereConnected (suc (suc m + suc n))) ) _ _) _ _ .fst)
    where
    fstEq : PathP _ _ _
    fstEq = toPathP (funExt (λ s
      → ((transportRefl _
        ∙ cong (sphere→Join (suc m) (suc n))
           (sym (substCommSlice (λ n → S₊ (suc n)) (λ n → S₊ (suc n))
                                (λ _ → -S^ (suc (suc m · suc n)))
                                (sym (+-comm (suc m) (suc n)))
                                (join→Sphere (suc n) (suc m)
                                  (sphere→Join (suc n) (suc m) s))
               ∙ cong (-S^ (suc (suc m · suc n)))
                      (cong (subst (S₊ ∘ suc) (sym (+-comm (suc m) (suc n))))
                            (Iso.rightInv (IsoSphereJoin (suc n) (suc m)) s)))))
        ∙ cong (sphere→Join (suc m) (suc n))
               (fromPathP (main' (sphere→Join (suc n) (suc m) s))))
        ∙ Iso.leftInv (IsoSphereJoin (suc m) (suc n))
                       (join-commFun (sphere→Join (suc n) (suc m) s))))

private
  assocPath : (n m l : ℕ) → _ ≡ _
  assocPath n m l = (+-assoc (suc m) (suc n) (suc l)
                          ∙ cong (_+ suc l) (+-comm (suc m) (suc n))
                          ∙ +-assoc (suc n) (suc m) (suc l) ⁻¹)

wh∘∙eq : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → {B' : Pointed ℓ'} → (e : B' ≃∙ B)
  → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
   ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e))
wh∘∙eq {A = A} {B} {C} {B'} =
  Equiv∙J (λ B' e → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
   ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e)))
   λ f g → cong (·whΣ A B f)
             (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g)
          ∙ (sym (∘∙-idˡ (·whΣ A B f g)))
          ∙ cong₂ _∘∙_ refl
              (sym (ΣPathP (suspFunIdFun , refl))
              ∙ cong suspFun∙ (sym
                 (cong fst ⋀→∙-idfun)))

wh∘∙eqL : ∀ {ℓ ℓ' ℓ''} {A A' : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (e : A' ≃∙ A)
  (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → ·whΣ A' B (f ∘∙ suspFun∙ (fst (fst e))) g
  ≡ (·whΣ A B f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ B))
wh∘∙eqL {A = A} {B} {C} {B'} =
  Equiv∙J (λ B e → (f : Susp∙ (typ A) →∙ B')
      (g : Susp∙ (typ C) →∙ B') →
      ·whΣ B C (f ∘∙ suspFun∙ (fst (fst e))) g ≡
      (·whΣ A C f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ C)))
    λ f g → cong₂ (·whΣ A C) (cong (f ∘∙_) suspFun∙IdFun ∙ ∘∙-idˡ f) refl
           ∙ sym (∘∙-idˡ _)
           ∙ cong₂ _∘∙_ refl (sym
              (cong suspFun∙ (cong fst ⋀→∙-idfun)
              ∙ suspFun∙IdFun))

-- Technical lemma
private
  retEqIsoToEquiv∙ : ∀ {ℓ} {A B : Pointed ℓ}
    (e : A ≃∙ B) (e∙ : invEq (fst e) (pt B) ≡ pt A)
    (eq : sym (secEq (fst e) (pt B))
        ∙ cong (fst (fst e)) e∙
        ≡ sym (snd e))
      → retEq (fst e) (pt A)
       ≡ cong (invEq (fst e)) (snd e)
       ∙ e∙
  retEqIsoToEquiv∙ {A = A} {B} =
    Equiv∙J (λ A e → (e∙ : invEq (fst e) (pt B) ≡ pt A)
                      (eq : sym (secEq (fst e) (pt B))
                          ∙ cong (fst (fst e)) e∙
                          ≡ sym (snd e))
      → retEq (fst e) (pt A) ≡ cong (invEq (fst e)) (snd e) ∙ e∙)
      λ e∙ p → sym p

[]≡·whΣ' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
  (f : S₊∙ (suc n) →∙ X) (g : S₊∙ (suc m) →∙ X)
  →  [ f ∣ g ]
   ≡ (·whΣ (S₊∙ n) (S₊∙ m)
           (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
           (g ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))
    ∘∙ (suspFun∙ (inv (SphereSmashIso n m))
    ∘∙ (fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m))))
[]≡·whΣ' {X = X} {n} {m} f g =
  cong₂ _∘∙_ ((cong₂ [_∣_]-pre
        (sym (∘∙-idˡ _)
        ∙ cong₂ _∘∙_ refl (sym (IsoSucSphereSusp≃∙CompR n))
        ∙ sym (∘∙-assoc f _ _))
        (sym (∘∙-idˡ _)
        ∙ cong₂ _∘∙_ refl (sym (IsoSucSphereSusp≃∙CompR m))
        ∙ sym (∘∙-assoc g _ _)))) refl
  ∙ cong₂ _∘∙_
     (cong (joinPinch∙ (S₊∙ n) (S₊∙ m) X) (funExt (λ a → funExt λ b →
       cong₂ _∙_ (Ω→lemma m b g) (Ω→lemma n a f))))
     (ΣPathP (refl , sym (lem' n m) ∙ lUnit _))
  ∙ cong₂ _∘∙_ (·whΣ≡·wh (S₊∙ n) (S₊∙ m)
           (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
           (g ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)))
           (refl {x = ≃∙map (invEquiv∙ (joinSphereEquiv∙ n m))})
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl
          (cong (_∘∙ ≃∙map (invEquiv∙ (joinSphereEquiv∙ n m)))
                (lem n m)
          ∙ ∘∙-assoc _ _ _
          ∙ cong₂ _∘∙_ refl
            ((cong₂ _∘∙_ (sym (∘∙-idˡ _)) refl)
            ∙ rightInv (post∘∙equiv (joinSphereEquiv∙ n m)) (idfun∙ _))
          ∙ ∘∙-idˡ _)
  where
  Ω→lemma : (n : ℕ) (a : S₊ n) (f : S₊∙ (suc n) →∙ X)
    → Ω→ ((f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))
                ∘∙ ≃∙map (IsoSucSphereSusp≃∙ n)) .fst (σS a)
     ≡ Ω→ (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) .fst (σ (S₊∙ n) a)
  Ω→lemma n a f =
      cong (λ f → Ω→ f .fst (σS a))
        ((∘∙-assoc f _ _
        ∙ cong₂ _∘∙_ refl (IsoSucSphereSusp≃∙CompR n))
       ∙ ∘∙-idˡ f)
    ∙ Ω→comp-σS n f a

  lemL : (n m : ℕ) →
      suspFun (inv (SphereSmashIso n m))
      (fun (IsoSucSphereSusp (n + m)) (ptSn (suc (n + m))))
    ≡ north
  lemL zero zero = refl
  lemL zero (suc m) = refl
  lemL (suc n) m = refl

  lemR : (n m : ℕ) →
      suspFun (inv (SphereSmashIso n m))
      (fun (IsoSucSphereSusp (n + m)) (ptSn (suc (n + m))))
    ≡ south
  lemR zero zero = merid (inl tt)
  lemR zero (suc m) = merid (inl tt)
  lemR (suc n) m = merid (inl tt)

  lemma : (n m : ℕ) (a : S₊ n) (b : S₊ m)
    → Square {A = Susp (S₊∙ n ⋀ S₊∙ m)}
              (merid (inr (a , b)))
              (cong (suspFun (inv (SphereSmashIso n m)))
               (cong (fun (IsoSucSphereSusp (n + m)))
                (cong (fst (fst (joinSphereEquiv∙ n m))) (push a b))))
              (sym (lemL n m))
              (sym (lemR n m))
  lemma zero zero false false =
    compPath-filler (merid (inr (false , false))) (sym (merid (inl tt)))
      ▷ (cong₂ _∙_ refl (cong (sym ∘ merid) (push (inl false)))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero zero))) _ _))
  lemma zero zero false true =
    cong merid (sym (push (inl false))) ◁ λ i j → merid (inl tt) (~ i ∧ j)
  lemma zero zero true b =
    cong merid (sym (push (inr b))) ◁ λ i j → merid (inl tt) (~ i ∧ j)
  lemma zero (suc m) false b =
      compPath-filler (merid (inr (false , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_ refl (cong (sym ∘ merid) (push (inl false)))
    ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero (suc m)))) _ _))
  lemma zero (suc m) true b =
    cong merid (sym (push (inr b)))
    ◁ compPath-filler (merid (inl tt)) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_ (cong merid (push (inl false)))
                 (cong (sym ∘ merid) (push (inl false)))
    ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso zero (suc m)))) _ _))
  lemma (suc n) zero a b =
    compPath-filler (merid (inr (a , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_
       (cong merid (sym (leftInv (SphereSmashIso (suc n) zero)
                          (inr (a , b)))))
       (cong (sym ∘ merid) (sym (SphereSmashIso⁻∙ (suc n) zero)))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso (suc n) zero))) _ _))
  lemma (suc n) (suc m) a b =
    compPath-filler (merid (inr (a , b))) (sym (merid (inl tt)))
    ▷ (cong₂ _∙_
       (cong merid (sym (leftInv (SphereSmashIso (suc n) (suc m))
                          (inr (a , b)))))
       (cong (sym ∘ merid) (sym (SphereSmashIso⁻∙ (suc n) (suc m))))
      ∙ sym (cong-∙ (suspFun (inv (SphereSmashIso (suc n) (suc m)))) _ _))

  lem : (n m : ℕ)
    → Join→SuspSmash∙ (S₊∙ n) (S₊∙ m)
    ≡ (suspFun∙ (inv (SphereSmashIso n m))
    ∘∙ (fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m)))
    ∘∙ ≃∙map (joinSphereEquiv∙ n m)
  lem n m i .fst (inl x) = lemL n m (~ i)
  lem n m i .fst (inr x) = lemR n m (~ i)
  lem n m i .fst (push a b j) = lemma n m a b i j
  lem zero zero i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j
  lem zero (suc m) i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j
  lem (suc n) m i .snd j =
    (sym (lUnit (refl ∙ λ _ → north)) ∙ sym (lUnit refl)) (~ i) j

  F : _ →∙ _
  F = fun (IsoSucSphereSusp (n + m)) , IsoSucSphereSusp∙' (n + m)

  p1 : (n m : ℕ) → leftInv (joinSphereIso' (suc n) m) (inl (ptSn (suc n)))
                    ≡ sym (push (ptSn (suc n)) (ptSn m))
  p1 n m =
    cong₂ _∙_ (cong (congS (inv (invIso SmashJoinIso))) (sym (rUnit refl))) refl
     ∙ sym (lUnit _)

  p2 : (n m : ℕ) → rightInv (joinSphereIso' (suc n) m) (ptSn (suc (suc n + m)))
                  ≡ sym (merid (ptSn (suc n + m)))
  p2 n m = cong₂ _∙_ (cong (sym ∘ merid) (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))))
       (sym (rUnit refl))
       ∙ sym (rUnit _)

  compPath-filler-diag : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → Path (Path A _ _) (λ i → compPath-filler p q (~ i) i) p
  compPath-filler-diag p q j i = compPath-filler p q (~ i ∧ ~ j) i

  p3 : (m : ℕ) → push true (ptSn (suc m))
                ∙ leftInv (joinSphereIso' zero (suc m)) (inl true)
                ≡ refl
  p3 m = cong₂ _∙_ refl
      (cong₂ _∙_ (cong (congS (fun SmashJoinIso))
                       (sym (rUnit (λ _ → north)))) refl
      ∙ sym (lUnit _))
    ∙ rCancel (push true (ptSn (suc m)))

  lem' :  (n m : ℕ) → retEq (isoToEquiv (IsoSphereJoin n m)) (inl (ptSn n))
                       ≡ IsoSphereJoin⁻Pres∙ n m
  lem' n m = retEqIsoToEquiv∙
    (isoToEquiv (IsoSphereJoin n m) , IsoSphereJoinPres∙ n m)
    (IsoSphereJoin⁻Pres∙ n m) (oh n m)
    ∙ sym (lUnit (IsoSphereJoin⁻Pres∙ n m))
    where
    dd = join→Sphere≡

    lemma3 : (n m : ℕ)
      → (λ i → join→Sphere≡ (suc n) m
                 (push (ptSn (suc n)) (ptSn m) (~ i)) (~ i))
       ≡ sym (merid (ptSn (suc (n + m))))
    lemma3 n m = flipSquare
      ((λ i j → join→Sphere≡ (suc n) m
                      (push (ptSn (suc n)) (ptSn m) (~ i ∨ j)) (~ i))
     ▷ (cong σS (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))) ∙ σS∙))

    oh : (n m : ℕ)
      → sym (secEq (isoToEquiv (IsoSphereJoin n m)) (ptSn (suc (n + m))))
       ∙ cong (join→Sphere n m) (IsoSphereJoin⁻Pres∙ n m)
       ≡ sym (IsoSphereJoinPres∙ n m)
    oh zero zero =
      cong₂ _∙_ (cong sym (sym (lUnit _)
               ∙ sym (lUnit (refl ∙ refl)) ∙ sym (rUnit refl))) refl
     ∙ sym (rUnit refl)
    oh zero (suc n) =
        cong₂ _∙_ (cong₃ _∙∙_∙∙_
          (cong sym (cong₂ _∙_ refl (sym (rUnit refl)) ∙ sym (rUnit _)))
          (λ j i → compPath-filler (merid (ptSn (suc n)))
                     (sym (merid (ptSn (suc n)))) (i ∧ ~ j) (~ i))
          refl) refl
      ∙ cong sym (sym (rUnit _) ∙ rCancel (merid (ptSn (suc n))))
    oh (suc n) m = cong₂ _∙_ (cong₃ _∙∙_∙∙_
      (cong sym (cong₂ _∙_ refl (sym (rUnit refl)) ∙ sym (rUnit _))
              ∙ cong merid (IdL⌣S {n = suc n} {m = m} (ptSn (suc n))))
                             (lemma3 n m) refl
                           ∙ cong sym (rCancel (merid (ptSn (suc (n + m))))))
                           refl
                           ∙ sym (rUnit refl)

[]≡·whΣ : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  →  [ f ∣ g ]
   ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g
   ∘∙ suspFun∙ (inv (SphereSmashIso (suc n) (suc m))))
[]≡·whΣ {X = X} {n} {m} f g = []≡·whΣ'  {X = X} f g
  ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)))
               (∘∙-idˡ f) (∘∙-idˡ g))
               (∘∙-idˡ (suspFun∙ (inv (SphereSmashIso (suc n) (suc m)))))

tripleSmasherL≃∙ : {n m l : ℕ}
  → S₊∙ (suc n + (suc m + suc l))
  ≃∙ S₊∙ (suc n) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))
tripleSmasherL≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m + suc l)))
                        , SphereSmashIso⁻∙ (suc n) (suc m + suc l))
             (⋀≃ (idEquiv∙ (S₊∙ (suc n)))
             ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l))))
                                , (SphereSmashIso⁻∙ (suc m) (suc l)))
            , refl)

tripleSmasherR≃∙ : {n m l : ℕ}
  → S₊∙ ((suc n + suc m) + suc l)
  ≃∙ ((S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) ⋀∙ S₊∙ (suc l))
tripleSmasherR≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n + suc m) (suc l)))
                        , SphereSmashIso⁻∙ (suc n + suc m) (suc l))
             (⋀≃ ((isoToEquiv (invIso (SphereSmashIso (suc n) (suc m))))
                                    , (SphereSmashIso⁻∙ (suc n) (suc m)))
                 (idEquiv∙ (S₊∙ (suc l)))
            , refl)

tripleSmasherL≃∙Id : (n m l : ℕ) (x : _)
  → PathP (λ i → Susp (S₊ (assocPath n m l (~ i))))
           (suspFun (-S^ (suc n · suc m)
                   ∘ invEq (fst (tripleSmasherL≃∙ {n = n} {m} {l}))) x)
           (suspFun (invEq (fst (tripleSmasherL≃∙ {n = m} {n} {l}))
                   ∘ inv SmashAssocIso
                   ∘ (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                   ∘ fun SmashAssocIso) x)
tripleSmasherL≃∙Id n m l north i = north
tripleSmasherL≃∙Id n m l south i = south
tripleSmasherL≃∙Id n m l (merid a i) j = lem a j i
  where
  lemma : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
    → PathP (λ i → S₊ (assocPath n m l (~ i)))
             (-S^ (suc n · suc m) (invEq (fst tripleSmasherL≃∙)
               (inr (x , inr (y , z)))))
              (invEq (fst tripleSmasherL≃∙)
               (inv SmashAssocIso
                ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                 (fun SmashAssocIso (inr (x , inr (y , z)))))))
  lemma x y z = transport (λ j →
    PathP (λ i → S₊ (isSetℕ _ _ p (sym (assocPath n m l)) j i))
          (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
          (y ⌣S (x ⌣S z)))
        help
    where
    p = (cong suc (+-assoc n (suc m) (suc l))
       ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
       ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

    help : PathP (λ i → S₊ (p i))
                 (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
                 (y ⌣S (x ⌣S z))
    help =
      compPathP' {B = S₊}
      (compPathP' {B = S₊}
        (λ i → -S^ (suc n · suc m) (assoc⌣S x y z i))
        (λ i → -S^ (suc n · suc m)
           (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
                    (sym (comm⌣S x y)) (~ i) ⌣S z))
      ▷ (cong (-S^ (suc n · suc m))
                (⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
               ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))
      ∙ -S^² (suc n · suc m) ((y ⌣S x) ⌣S z)))
      (symP (assoc⌣S y x z))

  lem : (a : _)
    → SquareP (λ i j → Susp (S₊ (assocPath n m l (~ i))))
               (merid ((-S^ (suc n · suc m) ∘ invEq (fst tripleSmasherL≃∙)) a))
               (merid (invEq (fst tripleSmasherL≃∙)
                        (inv SmashAssocIso
                         ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                          (fun SmashAssocIso a)))))
               (λ _ → north)
               (λ _ → south)
  lem = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
    λ x → ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
      λ y z i → merid (lemma x y z i)

·whΣ-assocer : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  (h : S₊∙ (2 + l) →∙ X)
  → [ f ∣ [ g ∣ h ] ]
   ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) f
       (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h)
   ∘∙ suspFun∙ (fst (fst tripleSmasherL≃∙)))
·whΣ-assocer {X = X} {n} {m} {l} f g h =
    cong₂ [_∣_] refl ([]≡·whΣ {X = X} g h)
  ∙ []≡·whΣ f _
  ∙ cong₂ _∘∙_
      (wh∘∙eq ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l))))
                                 , (SphereSmashIso⁻∙ (suc m) (suc l))) f
             (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h))
      refl
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl (sym (suspFun∙Comp _ _))

·whΣ-assocerR : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  (h : S₊∙ (2 + l) →∙ X)
  → [ [ f ∣ g ] ∣ h ]
   ≡ (·whΣ (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l))
       (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h
   ∘∙ suspFun∙ ((fst (fst tripleSmasherR≃∙))))
·whΣ-assocerR {X = X} {n} {m} {l} f g h =
  cong₂ [_∣_]  ([]≡·whΣ {X = X} f g) refl
  ∙ []≡·whΣ _ _
  ∙ cong₂ _∘∙_ (wh∘∙eqL (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m)))
                                 , (SphereSmashIso⁻∙ (suc n) (suc m)))
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h) refl
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl
    (sym (suspFun∙Comp _ _))


[∣]π'-distrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f g : π' (suc (suc n)) X) (h : π' (suc m) X)
       → [ ·π' (suc n) f g ∣ h ]π'
          ≡ ·π' _ [ f ∣ h ]π' [ g ∣ h ]π'
[∣]π'-distrL {X = X} {n} {m} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
       (lem n m (·Susp (S₊∙ (suc n)) f g) h
     ∙ (cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc n) m)))
              (WhiteheadProdΣBilinₗ
                (S₊∙ (suc n)) (S₊∙ n) (IsoSucSphereSusp≃∙ n) (S₊∙ m) f g (h *))
     ∙ cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc n) m)))
         (·Susp-suspFun (S₊∙ (suc n) ⋀∙ (S₊ m , ptSn m)) (S₊∙ (suc (n + m)))
            (isoToEquiv (SphereSmashIso (suc n) m) , refl)
            (·whΣ (S₊∙ (suc n)) (S₊ m , ptSn m) f (h *))
            (·whΣ (S₊∙ (suc n)) (S₊ m , ptSn m) g (h *)))
     ∙ ∘∙-assoc _ _ _
     ∙ cong₂ _∘∙_ refl
       (sym (suspFun∙Comp (fun (SphereSmashIso (suc n) m))
                     (inv (SphereSmashIso (suc n) m)))
     ∙ cong suspFun∙ (funExt (rightInv (SphereSmashIso (suc n) m)))
     ∙ suspFun∙IdFun)
     ∙ ∘∙-idˡ _)
     ∙ cong₂ (·Susp (S₊∙ (suc (n + m))))
             (sym (lem n m f h))
             (sym (lem n m g h)))
  where
  _* : {m : ℕ} (h : S₊∙ (suc m) →∙ X) → _
  _* {m = m} h = h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)

  module _ (n m : ℕ) (f : S₊∙ (suc (suc n)) →∙ X) (h : S₊∙ (suc m) →∙ X) where
    lem : [ f ∣ h ]
        ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ m) f (h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))
          ∘∙ (suspFun∙ (inv (SphereSmashIso (suc n) m))))
    lem = []≡·whΣ' f h
        ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ (suc n)) (S₊∙ m)) (∘∙-idˡ f) refl)
                     (∘∙-idˡ (suspFun∙ (inv (SphereSmashIso (suc n) m))))

[∣]π'-distrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc n) X) (g h : π' (suc (suc m)) X)
       → [ f ∣ ·π' (suc m) g h ]π'
          ≡ ·π' _ [ f ∣ g ]π' [ f ∣ h ]π'
[∣]π'-distrR {X = X} {n} {m} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
      ([]≡·whΣ' f (·Susp (S₊∙ (suc m)) g h)
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m))) refl
                    (∘∙-idˡ (·Susp (S₊∙ (suc m)) g h))) refl
      ∙ cong₂ _∘∙_ (WhiteheadProdΣBilinᵣ (S₊∙ n) (S₊∙ (suc m)) (S₊∙ m) (IsoSucSphereSusp≃∙ m)
                    (f *) g h) refl
      ∙ main n m f g h
      ∙ cong₂ ∙Π (cong₂ _∘∙_
        (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m)) ) refl (sym (∘∙-idˡ g))) refl
        ∙ sym ([]≡·whΣ' f g))
        (cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ (suc m)) ) refl (sym (∘∙-idˡ h))) refl
        ∙ sym ([]≡·whΣ' f h)))
  where
  cor : (n m : ℕ) → _ →∙ _
  cor n m =
    (suspFun∙ (inv (SphereSmashIso n (suc m))) ∘∙
     (fun (IsoSucSphereSusp (n + suc m)) ,
      IsoSucSphereSusp∙' (n + suc m)))

  _* : {m : ℕ} (h : S₊∙ (suc m) →∙ X) → _
  _* {m = m} h = h ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m)

  main : (n m : ℕ) (f : S₊∙ (suc n) →∙ X) (g h : S₊∙ (suc (suc m)) →∙ X)
    → (·Susp (S₊∙ n ⋀∙ S₊∙ (suc m))
              (·whΣ (S₊∙ n) (S₊∙ (suc m)) (f *) g)
              (·whΣ (S₊∙ n) (S₊∙ (suc m)) (f *) h)
       ∘∙ cor n m)
    ≡ ∙Π (·whΣ (S₊∙ n) (S₊∙ (suc m))
               (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) g
       ∘∙ cor n m)
         (·whΣ (S₊∙ n) (S₊∙ (suc m))
               (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n)) h
       ∘∙ cor n m)
  main zero m f g h =
      cong₂ _∘∙_ (·Susp-suspFun (S₊∙ zero ⋀∙ S₊∙ (suc m))
                 (S₊∙ (suc m))
                 (isoToEquiv (SphereSmashIso zero (suc m)) , refl)
                 (·whΣ (S₊∙ zero) (S₊∙ (suc m)) (f *) g)
                 (·whΣ (S₊∙ zero) (S₊∙ (suc m)) (f *) h))
                 (∘∙-idˡ (suspFun∙ (λ y → inr (false , y))))
    ∙ ∘∙-assoc _ _ _
    ∙ cong₂ _∘∙_ refl
        (ΣPathP (funExt (secEq (isoToEquiv
                  (congSuspIso (SphereSmashIso zero (suc m)))))
                  , sym (rUnit refl)))
    ∙ ∘∙-idˡ _
    ∙ cong₂ (·Susp (S₊∙ (suc m)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
  main (suc n) m f g h =
    cong₂ _∘∙_ (·Susp-suspFun (S₊∙ (suc n) ⋀∙ S₊∙ (suc m))
               (S₊∙ (suc (n + suc m)))
               (isoToEquiv (SphereSmashIso (suc n) (suc m)) , refl)
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) (f *) g)
               (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) (f *) h)) refl
    ∙ ∘∙-assoc _ _ _
    ∙ cong₂ _∘∙_ refl (ΣPathP
      ((funExt (secEq (isoToEquiv (congSuspIso (SphereSmashIso (suc n) (suc m))))))
      , sym (rUnit _)
      ∙ cong (congS (suspFun (fun (SphereSmashIso (suc n) (suc m)))))
                    (sym (rUnit refl))))
    ∙ ∘∙-idˡ _
    ∙ cong₂ (·Susp (S₊∙ (suc (n + suc m))))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))
            (cong₂ _∘∙_ refl (sym (∘∙-idˡ _)))


[∣]π'-idL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
   (g : π' (suc m) X) → [ 1π' (suc n) ∣ g ]π' ≡ 1π' (suc (n + m))
[∣]π'-idL {n = n} {m} =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ ([]≡·whΣ' 1Π f
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ m))
                          (ΣPathP (refl , sym (rUnit refl))) refl
      ∙ WhiteheadProdΣIdL (S₊∙ n) (S₊∙ m)
         (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ m))) refl
      ∙ ΣPathP (refl , (sym (rUnit refl))))

[∣]π'-idR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
   (f : π' (suc n) X) → [ f ∣ 1π' (suc m) ]π' ≡ 1π' (suc (n + m))
[∣]π'-idR {n = n} {m} =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ ([]≡·whΣ' f 1Π
      ∙ cong₂ _∘∙_ (cong₂ (·whΣ (S₊∙ n) (S₊∙ m)) refl
                          (ΣPathP (refl , sym (rUnit refl)))
      ∙ WhiteheadProdΣIdR (S₊∙ n) (S₊∙ m)
         (f ∘∙ ≃∙map (IsoSucSphereSuspInv≃∙ n))) refl
      ∙ ΣPathP (refl , (sym (rUnit refl))))

[∣]π'-invDistrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc m) X)
       → [ -π' (suc n) f ∣ g ]π'
        ≡ -π' (suc (n + m)) [ f ∣ g ]π'
[∣]π'-invDistrL {n = n} {m} f g =
    sym (sym (π'-assoc (suc (n + m)) [ -π' (suc n) f ∣ g ]π'
                                     [ f ∣ g ]π' (-π' (suc (n + m))
                                     [ f ∣ g ]π'))
    ∙ cong₂ (·π' (suc (n + m))) refl (π'-rCancel (suc (n + m)) [ f ∣ g ]π')
    ∙ π'-rUnit _ ([ -π' (suc n) f ∣ g ]π'))
  ∙ cong (λ x → ·π' (suc (n + m)) x (-π' (suc (n + m)) [ f ∣ g ]π'))
         (sym ([∣]π'-distrL (-π' (suc n) f) f g))
  ∙ cong₂ (·π' (suc (n + m)))
          (cong [_∣ g ]π' (π'-lCancel (suc n) f) ∙ [∣]π'-idL g) refl
  ∙ π'-lUnit _ (-π' (suc (n + m)) [ f ∣ g ]π')

[∣]π'-invDistrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc n) X) (g : π' (suc (suc m)) X)
       → [ f ∣ -π' (suc m) g ]π'
        ≡ -π' (n + suc m) [ f ∣ g ]π'
[∣]π'-invDistrR {n = n} {m} f g =
    sym (sym (π'-assoc (n + suc m)
               [ f ∣ -π' (suc m) g ]π'
               [ f ∣ g ]π'
               (-π' (n + suc m) [ f ∣ g ]π'))
    ∙ cong₂ (·π' (n + suc m)) refl
            (π'-rCancel (n + suc m) [ f ∣ g ]π')
    ∙ π'-rUnit _ ([ f ∣ -π' (suc m) g ]π'))
  ∙ cong (λ x → ·π' (n + suc m) x (-π' (n + suc m) [ f ∣ g ]π'))
         (sym ([∣]π'-distrR f (-π' (suc m) g) g))
  ∙ cong₂ (·π' (n + suc m))
          (cong [ f ∣_]π' (π'-lCancel (suc m) g) ∙ [∣]π'-idR f) refl
  ∙ π'-lUnit _ (-π' (n + suc m) [ f ∣ g ]π')

[∣]π'-inv^DistrL : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ} (k : ℕ)
       (f : π' (suc (suc n)) X) (g : π' (suc m) X)
       → [ -π^ k f ∣ g ]π' ≡ -π^ k [ f ∣ g ]π'
[∣]π'-inv^DistrL {n = n} {m} zero f g = refl
[∣]π'-inv^DistrL {n = n} {m} (suc k) f g =
    [∣]π'-invDistrL (-π^ k f) g
  ∙ cong (-π' _) ([∣]π'-inv^DistrL k f g)

[∣]π'-inv^DistrR : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ} (k : ℕ)
       (f : π' (suc n) X) (g : π' (suc (suc m)) X)
       → [ f ∣ -π^ k g ]π' ≡ -π^ k [ f ∣ g ]π'
[∣]π'-inv^DistrR {n = n} {m} zero f g = refl
[∣]π'-inv^DistrR {n = n} {m} (suc k) f g =
    [∣]π'-invDistrR f (-π^ k g)
  ∙ cong (-π' _) ([∣]π'-inv^DistrR k f g)

[_∣_]π'Jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : π' (suc (suc n)) X)
  (g : π' (suc (suc m)) X)
  (h : π' (suc (suc l)) X)
  → [ f ∣ [ g ∣ h ]π' ]π'
   ≡ ·π' _ (subst (λ k → π' k X)
                  (cong (2 +_) (sym (+-assoc n (suc m) (suc l))))
                  ([ [ f ∣ g ]π' ∣ h ]π'))
           (subst (λ k → π' k X)
                  (cong suc (assocPath n m l))
                  (-π^ (suc n · suc m) [ g ∣ [ f ∣ h ]π' ]π'))
[_∣_]π'Jacobi {X = X} {n} {m} {l} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
       (·whΣ-assocer f g h
      ∙ cong₂ _∘∙_
        (JacobiΣR' (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
          (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
          (S₊∙ (suc l)) (S₊∙ l)
          (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
          f g h) refl
      ∙ cong₂ _∘∙_ (·Susp-suspFun _ _ (invEquiv∙ tripleSmasherL≃∙) _ _) refl
      ∙ ∘∙-assoc _ _ _
      ∙ cong₂ _∘∙_ refl
        (sym (suspFun∙Comp _ _)
        ∙ cong suspFun∙ (funExt (retEq (fst tripleSmasherL≃∙))) ∙ suspFun∙IdFun)
      ∙ ∘∙-idˡ _
      ∙ cong₂ (·Susp (S₊∙ (suc (n + suc (m + suc l)))))
              (sym (sym (subst∙Id (S₊∙ ∘ (2 +_))
                          (sym (+-assoc n (suc m) (suc l)))
                          [ [ f ∣ g ] ∣ h ])
                 ∙ cong₂ _∘∙_ (·whΣ-assocerR f g h) (λ _ → s1)
                 ∙ ∘∙-assoc _ _ _
                 ∙ cong₂ _∘∙_ refl (ΣPathP ((funExt λ { north → refl
                                                      ; south → refl
                                                      ; (merid a i) j → hoo a j i})
                                                      , sym (rUnit refl)) ∙ suspFun∙Comp _ _)
                 ∙ sym (∘∙-assoc _ _ _)))
              (sym (cong (transport (λ i → S₊∙ (suc (assocPath n m l i)) →∙ X))
                         (iter-Π≡∘-S^ deg _)
                  ∙ (sym (subst∙Id (S₊∙ ∘ suc)
                          (assocPath n m l) _)
                  ∙ cong₂ _∘∙_ (cong₂ _∘∙_ (·whΣ-assocer g f h)
                                          (-S^∙suspFun deg)
                             ∙ ∘∙-assoc _ _ _
                             ∙ cong₂ _∘∙_ refl
                               (sym (suspFun∙Comp (fst (fst tripleSmasherL≃∙))
                                                  (-S^ deg)))) refl)
                  ∙ ∘∙-assoc _ _ _
                  ∙ cong₂ _∘∙_ refl
                    ((cong₂ _∘∙_ refl
                      refl
                    ∙ sym (suspFun∙substLem (sym (assocPath n m l))
                            (fst (fst tripleSmasherL≃∙) ∘ -S^ deg))
                    ∙ final-lemma)
                    ∙ suspFun∙Comp _ _)
                  ∙ sym (∘∙-assoc _ _ _))))
       ∙ refl
       ∙ cong₂ (·π' (suc (n + suc (m + suc l)))) refl
               (cong (subst (λ k → π' k X) (cong suc (assocPath n m l)))
                     (sym (-π^≡iter-Π deg _)))
  where
  suspFun∙substLem : ∀ {ℓ} {X : Type ℓ} {n m : ℕ}
    (p : suc n ≡ suc m)
    (f : S₊ (suc m)  → X)
    → suspFun∙ (f ∘ subst S₊ p)
    ≡ suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p
  suspFun∙substLem p f =
    cong (λ p → suspFun∙ (f ∘ subst S₊ p)) (isSetℕ _ _ p (cong suc (cong predℕ p)))
    ∙ ∘∙preSubstLem _ _ _ f
    ∙ cong (λ p → suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p) (isSetℕ _ _ (cong suc (cong predℕ p)) p)
    where
    ∘∙preSubstLem : ∀ {ℓ} {X : Type ℓ} (n m : ℕ)
      (p : n ≡ m)
      (f : S₊ (suc m) → X)
      → suspFun∙ (f ∘ subst S₊ (cong suc p))
      ≡ (suspFun∙ f ∘∙ subst∙ (S₊∙ ∘ suc) (cong suc p))
    ∘∙preSubstLem n = J> λ f
      → (cong suspFun∙ (funExt (λ x → cong f (transportRefl x)))
      ∙ sym (∘∙-idˡ _))
      ∙ cong₂ _∘∙_ refl (sym (subst∙refl S₊∙))

  deg = suc n · suc m

  meridLem1 : (a : S₊ (suc (n + suc (m + suc l))))
    → merid (fst (fst tripleSmasherL≃∙)
              (-S^ deg (subst S₊ (sym (assocPath n m l)) a)))
     ≡ merid (inv SmashAssocIso
              ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
               (fun SmashAssocIso (fst (fst tripleSmasherL≃∙) a))))
  meridLem1 a =
      cong merid (cong (fst (fst tripleSmasherL≃∙)
                      ∘ -S^ deg
                      ∘ subst S₊ (sym (assocPath n m l)))
                 (sym (retEq (fst tripleSmasherL≃∙) a)))
    ∙ meridLem2 (fst (fst tripleSmasherL≃∙) a)
    where
    meridLem2 : (a : _)
      → merid (fst (fst tripleSmasherL≃∙)
                (-S^ deg
                 (subst S₊ (sym (assocPath n m l))
                  (invEq (fst tripleSmasherL≃∙) a))))
       ≡ merid (inv SmashAssocIso
                ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
                 (fun SmashAssocIso a)))
    meridLem2 =
      ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
       λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
         λ y z → cong merid
           (refl
           ∙ cong (fst (fst tripleSmasherL≃∙) ∘ -S^ deg)
                 (meridLem3 x y z)
          ∙ cong (fst (fst tripleSmasherL≃∙))
                 (-S^² deg _)
          ∙ secEq (fst tripleSmasherL≃∙) (inr (y , inr (x , z))))
      where
      p = (cong suc (+-assoc n (suc m) (suc l))
         ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
         ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

      meridLem3 : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
        → subst S₊ (sym (assocPath n m l))
                    (x ⌣S (y ⌣S z))
         ≡ -S^ deg (y ⌣S (x ⌣S z))
      meridLem3 x y z =
         cong (λ P → subst S₊ P (x ⌣S (y ⌣S z)))
              (isSetℕ _ _ _ _)
       ∙ fromPathP
          (compPathP' {B = S₊}
          (compPathP' {B = S₊}
            (λ i → (assoc⌣S x y z i))
            (λ i →
               (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
                       (sym (comm⌣S x y)) (~ i) ⌣S z))
          ▷ ((⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
                  ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))))
         (λ i → -S^ deg (assoc⌣S y x z (~ i))))

  final-lemma : suspFun∙
      ((λ x → fst (fst tripleSmasherL≃∙) (-S^ deg x)) ∘
       subst S₊ (λ i → assocPath n m l (~ i)))
      ≡
      suspFun∙
      ((inv SmashAssocIso ∘
        (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l))) ∘ fun SmashAssocIso)
       ∘ invEq (invEquiv (fst tripleSmasherL≃∙)))
  final-lemma = ΣPathP ((
    funExt (λ { north → refl
              ; south → refl
              ; (merid a i) j → meridLem1 a j i}))
    , refl)


  s1 = subst∙ (S₊∙ ∘ (2 +_)) (+-assoc n (suc m) (suc l))
  s2 = subst∙ (S₊∙ ∘ suc) (sym (assocPath n m l))

  hoo : (a : S₊ (suc (n + (suc m + suc l))))
    → cong (suspFun (fst (fst tripleSmasherR≃∙)) ∘ fst s1)
           (merid a)
    ≡ merid (fun SmashAssocIso (invEq (fst (invEquiv∙ tripleSmasherL≃∙)) a))
  hoo a = (λ j i → suspFun (fst (fst tripleSmasherR≃∙))
                     (transp (λ i → S₊ (suc (suc
                       (+-assoc n (suc m) (suc l) (i ∨ j))))) j
                     (merid (transp (λ i → S₊ (suc
                       (+-assoc n (suc m) (suc l) (i ∧ j))))
                                    (~ j) a) i)))
        ∙ cong (merid ∘ fst (fst tripleSmasherR≃∙)
              ∘ subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l)))
             (sym (retEq (fst tripleSmasherL≃∙) a))
        ∙ lem2 (fst (fst tripleSmasherL≃∙) a)
    where
    lem2 : (a : _) → merid (fst (fst tripleSmasherR≃∙)
                             (subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l))
                               (invEq (fst tripleSmasherL≃∙) a)))
                    ≡ merid (fun SmashAssocIso a)
    lem2 = ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
            λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
              λ y z →
       cong merid (cong (fst (fst tripleSmasherR≃∙))
                        (fromPathP (assoc⌣S x y z))
                ∙ secEq (fst tripleSmasherR≃∙) (inr (inr (x , y) , z)))


jacobiPath₁ : (p q r : ℕ)
  → suc (suc (q + suc (r + suc p))) ≡
      suc (suc (p + suc (q + suc r)))
jacobiPath₁ p q r =
  cong suc
    (+-assoc (suc q) (suc r) (suc p)
    ∙ sym (+-comm (suc p) (suc q + suc r)))

jacobiPath₂ : (p q r : ℕ)
  → suc (suc (r + suc (p + suc q)))
   ≡ suc (suc (p + suc (q + suc r)))
jacobiPath₂ p q r = cong suc
  (+-comm (suc r) (suc p + suc q)
  ∙ sym (+-assoc (suc p) (suc q) (suc r)))

[_∣_]π'Jacobi' : ∀ {ℓ} {X : Pointed ℓ} {p q r : ℕ}
  (f : π' (suc (suc p)) X)
  (g : π' (suc (suc q)) X)
  (h : π' (suc (suc r)) X)
  → ·π' _ (-π^ (p ·₋₁ r) [ f ∣ [ g ∣ h ]π' ]π')
      (·π' _ (subst (λ n → π' n X) (jacobiPath₁ p q r)
                    (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))
             (subst (λ n → π' n X) (jacobiPath₂ p q r)
                    (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π')))
   ≡ 1π' _
[_∣_]π'Jacobi' {X = X} {p} {q} {r} f g h =
  cong₂ _⋄_
        (cong (-π^ (p ·₋₁ r))
              ([_∣_]π'Jacobi f g h)
        ∙ AbGroupTheory.inv^Distr πX _ _ (p ·₋₁ r)
        ∙ λ _ → t1 ⋄ t2)
        (π'-comm _ t3 t4)
      ∙ comm-4 t1 t2 t4 t3
      ∙ cong₂ _⋄_ t1+t4≡0 t2+t3≡0
      ∙ π'-rUnit _ (1π' (suc (suc (p + suc (q + suc r)))))
  where
  πX : AbGroup _
  πX = Group→AbGroup (π'Gr ((suc p) + (suc q + suc r)) X)
                     (π'-comm _)

  open AbGroupTheory πX
  open GroupTheory (π'Gr ((suc p) + (suc q + suc r)) X)
  open AbGroupStr (snd πX) renaming (_+_ to _⋄_ ; -_ to -πX)

  evenOddLemma : (p q r : ℕ)
    → isEvenT (p ·₋₁ r + r ·₋₁ (p + suc q)) ≡ isOddT (r ·₋₁ q)
  evenOddLemma p q r = ua (propBiimpl→Equiv (isPropIsEvenT _) (isPropIsOddT _)
                          (fst main) (snd main))
   where
   _·₋₁'_ : {n : ℕ} → Expr n → Expr n → Expr n
   _·₋₁'_ a b = (K 1) +' (((K 1) +' a) ·' ((K 1) +' b))

   r·₋₁q : Expr 2
   r·₋₁q = (∣' zero) ·₋₁' (∣' one)

   p·₋₁r+r·₋₁[p+q+1] : Expr 3
   p·₋₁r+r·₋₁[p+q+1] = (∣' zero ·₋₁' ∣' two)
                   +' (∣' two ·₋₁' (∣' zero +' (K 1 +' ∣' one)))

   main : isEvenT (p ·₋₁ r + r ·₋₁ (p + suc q)) ↔ isOddT (r ·₋₁ q)
   main = main' (evenOrOdd r) (evenOrOdd q)
    where
    main' : isEvenT r ⊎ isOddT r → isEvenT q ⊎ isOddT q
          → isEvenT (p ·₋₁ r + r ·₋₁ (p + suc q)) ↔ isOddT (r ·₋₁ q)
    main' (inl evr) (inl odq) .fst e =
      ⊥.rec (¬evenAndOdd _ (e
        , solveIsOdd p·₋₁r+r·₋₁[p+q+1]
           ((p , ？) ∷ (q , yea odq) ∷ ((r , yea evr) ∷ []))))
    main' (inl evr) (inr x) .fst _ =
      solveIsOdd r·₋₁q ((r , yea evr) ∷ (q , nay x) ∷ [])
    main' (inl evr) (inl x) .snd s =
      ⊥.rec (¬evenAndOdd _
        (solveIsEven r·₋₁q ((r , yea evr) ∷ (q , yea x) ∷ []) , s))
    main' (inl evr) (inr odq) .snd odrq =
      solveIsEven p·₋₁r+r·₋₁[p+q+1]
        ((p , ？) ∷ (q , nay odq) ∷ ((r , yea evr) ∷ []))
    main' (inr odr) _ .fst _ = solveIsOdd r·₋₁q ((r , nay odr) ∷ (q , ？) ∷ [])
    main' (inr odr) evq .snd _ =
      solveIsEven p·₋₁r+r·₋₁[p+q+1] ((p , ？) ∷ (q , ？) ∷ ((r , nay odr) ∷ []))

  t1 = -π^ (p ·₋₁ r)
         (subst (λ n → π' n X)
                (cong (2 +_) (sym (+-assoc p (suc q) (suc r))))
         [ [ f ∣ g ]π' ∣ h ]π')

  t2 = -π^ (p ·₋₁ r)
         (subst (λ k → π' k X) (cong suc (assocPath p q r))
          (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π'))

  t3 = (subst (λ n → π' n X) (jacobiPath₁ p q r)
                  (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))

  t4 = (subst (λ n → π' n X) (jacobiPath₂ p q r)
                    (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π'))

  -π^-substComm : {n m : ℕ} (t : ℕ) (x : π' (suc n) X) (p : suc n ≡ suc m)
    → -π^ t (subst (λ k → π' k X) p x)
     ≡ subst (λ k → π' k X) p (-π^ t x)
  -π^-substComm t x p =
    cong (λ p → -π^ t (subst (λ k → π' k X) p x)) (isSetℕ _ _ p _)
    ∙ sym (substCommSlice (λ k → π' (suc k) X) (λ k → π' (suc k) X)
            (λ k → -π^ t) (cong predℕ p) x)
    ∙ cong (λ p → subst (λ k → π' k X) p (-π^ t x)) (isSetℕ _ _ _ p)

  t2≡ : -π^ (p ·₋₁ r)
        (subst (λ k → π' k X) (cong suc (assocPath p q r))
         (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π'))
      ≡ subst (λ k → π' k X) (jacobiPath₁ p q r)
           (-π^ (suc p · suc q)
             [ g ∣ [ h ∣ f ]π' ]π')
  t2≡ = -π^-substComm (p ·₋₁ r)
          (-π^ (suc p · suc q) [ g ∣ [ f ∣ h ]π' ]π')
          (cong suc (assocPath p q r))
      ∙ cong (subst (λ k → π' (suc k) X) (assocPath p q r))
             ((sym (iter+ (p ·₋₁ r) (suc p · suc q) (-π' _)
                   [ g ∣ [ f ∣ h ]π' ]π')
             ∙ cong (λ t → -π^ t [ g ∣ [ f ∣ h ]π' ]π')
                    (+-comm (p ·₋₁ r) (suc p · suc q)
                    ∙ cong ((suc p · suc q) +_)
                           (cong suc (·-comm (suc p) (suc r))))
             ∙ iter+ (suc p · suc q) (r ·₋₁ p) (-π' _)
                   [ g ∣ [ f ∣ h ]π' ]π'
             ∙ cong (-π^ (suc p · suc q))
                 ((cong (-π^ (r ·₋₁ p))
                    ((cong [ g ∣_]π' ([_∣_]π'-comm f h)
                   ∙ sym (substCommSlice (λ m → π' (suc m) X)
                                     (λ a → π' (suc (suc q + a)) X)
                                     (λ _ f → [ g ∣ f ]π')
                                     (+-comm (suc r) (suc p))
                                     (-π^ (r ·₋₁ p) [ h ∣ f ]π')))
                   ∙ cong (subst (λ a → π' (suc (suc q + a)) X)
                                 (+-comm (suc r) (suc p)))
                          ([∣]π'-inv^DistrR (r ·₋₁ p) g [ h ∣ f ]π'))
                 ∙ -π^-substComm (r ·₋₁ p) (-π^ (r ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π')
                     (λ i → suc (suc q + +-comm (suc r) (suc p) i))
                 ∙ cong (subst (λ k → π' k X)
                               (λ i → suc (suc q + +-comm (suc r) (suc p) i)))
                        (iter+iter (-π' _) (GroupTheory.invInv (π'Gr _ _))
                         (r ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π')))
             ∙ -π^-substComm (suc p · suc q) ([ g ∣ [ h ∣ f ]π' ]π')
                             (λ i → suc (suc q + +-comm (suc r) (suc p) i)))
            ∙ refl)
      ∙ compSubstℕ {A = λ n → π' n X}
          (λ i → suc (suc q + +-comm (suc r) (suc p) i))
          (cong suc (assocPath p q r))
          (jacobiPath₁ p q r)
          {(-π^ (suc p · suc q) [ g ∣ [ h ∣ f ]π' ]π')}

  t1≡ : t1 ≡ subst (λ n → π' n X) (jacobiPath₂ p q r)
                   (-π^ (p ·₋₁ r + r ·₋₁ (p + suc q))
                   [ h ∣ [ f ∣ g ]π' ]π')
  t1≡ = cong (-π^ (p ·₋₁ r)
         ∘ subst (λ n → π' n X)
                (cong (2 +_) (sym (+-assoc p (suc q) (suc r)))))
             ([_∣_]π'-comm ([ f ∣ g ]π') h)
      ∙ cong (-π^ (p ·₋₁ r))
             (compSubstℕ {A = λ n → π' n X}
               (cong suc (+-comm (suc r) (suc (p + suc q))))
               (sym (cong suc (+-assoc (suc p) (suc q) (suc r))))
               (jacobiPath₂ p q r))
      ∙ sym (substCommSlice
            (λ k → π' (suc k) X) (λ k → π' (suc k) X)
            (λ k → -π^ (p ·₋₁ r))
            (cong predℕ (jacobiPath₂ p q r))
            _)
      ∙ cong (subst (λ n → π' n X) (jacobiPath₂ p q r))
             (sym (iter+ (p ·₋₁ r) (r ·₋₁ (p + suc q)) (-π' _)
                     ([ h ∣ [ f ∣ g ]π' ]π'))
            ∙ refl)

  substHomLem : (n m : ℕ) (p : n ≡ m) {x y : π' (suc n) X}
    → ·π' _ (subst (λ n → π' (suc n) X) p x) (subst (λ n → π' (suc n) X) p y)
     ≡ subst (λ n → π' (suc n) X) p (·π' _ x y)
  substHomLem n = J> λ {x y} →
      cong₂ (·π' _) (transportRefl x) (transportRefl y)
    ∙ sym (transportRefl (·π' n x y))

  t1+t4≡0 : t1 ⋄ t4 ≡ 1π' _
  t1+t4≡0 = cong₂ _⋄_ t1≡ refl
          ∙ substHomLem _ _ (cong predℕ (jacobiPath₂ p q r))
          ∙ cong (subst (λ n → π' n X) (jacobiPath₂ p q r))
                 ((λ _ →
                   ·π' _ (-π^ (p ·₋₁ r + r ·₋₁ (p + suc q))
                              [ h ∣ [ f ∣ g ]π' ]π')
                         (-π^ (r ·₋₁ q) [ h ∣ [ f ∣ g ]π' ]π'))
               ∙ GroupTheory.-iter-odd+even (π'Gr _ _)
                   (suc (suc (r + p · suc r + r ·₋₁ (p + suc q))))
                   (r ·₋₁ q) ([ h ∣ [ f ∣ g ]π' ]π') (evenOddLemma p q r))
          ∙ λ j → transp (λ i → π' (jacobiPath₂ p q r (i ∨ j)) X) j
                    (1π' (jacobiPath₂ p q r j))

  t2+t3≡0 : t2 ⋄ t3 ≡ 1π' _
  t2+t3≡0 =
      cong₂ _⋄_ t2≡ refl
    ∙ substHomLem _ _ (cong predℕ (jacobiPath₁ p q r))
    ∙ cong (subst (λ n → π' n X) (jacobiPath₁ p q r))
           ((λ _ → ·π' _ (-π^ (suc p · suc q) [ g ∣ [ h ∣ f ]π' ]π')
                          (-π^ (q ·₋₁ p) [ g ∣ [ h ∣ f ]π' ]π'))
          ∙ GroupTheory.-iter-odd+even (π'Gr _ _) (suc p · suc q)
                           (q ·₋₁ p)
                           [ g ∣ [ h ∣ f ]π' ]π'
                           (cong isEvenT (·-comm (suc p) (suc q))))
    ∙ λ j → transp (λ i → π' (jacobiPath₁ p q r (i ∨ j)) X) j
                    (1π' (jacobiPath₁ p q r j))

-- We prove that the function joinTo⋁ used in the definition of the whitehead
-- product gives an equivalence between (Susp A × Susp B) and the
-- appropriate cofibre of joinTo⋁ (last two theorems in the following
-- module).

module _ (A B : Type) (a₀ : A) (b₀ : B) where
  private
    W = joinTo⋁ {A = (A , a₀)} {B = (B , b₀)}

  A∨B = (Susp A , north) ⋁ (Susp B , north)

  σB = σ (B , b₀)
  σA = σ (A , a₀)

  cofibW = Pushout W λ _ → tt

  whitehead3x3 :  3x3-span
  A00 whitehead3x3 = Susp A
  A02 whitehead3x3 = B
  A04 whitehead3x3 = Unit
  A20 whitehead3x3 = B
  A22 whitehead3x3 = A × B
  A24 whitehead3x3 = A
  A40 whitehead3x3 = B
  A42 whitehead3x3 = B
  A44 whitehead3x3 = Unit
  f10 whitehead3x3 _ = south
  f12 whitehead3x3 = snd
  f14 whitehead3x3 _ = tt
  f30 whitehead3x3 = idfun B
  f32 whitehead3x3 = snd
  f34 whitehead3x3 _ = tt
  f01 whitehead3x3 _ = north
  f21 whitehead3x3 = snd
  f41 whitehead3x3 = idfun B
  f03 whitehead3x3 _ = tt
  f23 whitehead3x3 = fst
  f43 whitehead3x3 _ = tt
  H11 whitehead3x3 x = merid (fst x)
  H13 whitehead3x3 _ = refl
  H31 whitehead3x3 _ = refl
  H33 whitehead3x3 _ = refl

  A0□→A∨B : A0□ whitehead3x3 → A∨B
  A0□→A∨B (inl x) = inl x
  A0□→A∨B (inr x) = inr north
  A0□→A∨B (push a i) = (push tt ∙ λ i → inr (σB a (~ i))) i

  A∨B→A0□ : A∨B → A0□ whitehead3x3
  A∨B→A0□ (inl x) = inl x
  A∨B→A0□ (inr north) = inl north
  A∨B→A0□ (inr south) = inl north
  A∨B→A0□ (inr (merid b i)) = (push b₀ ∙ sym (push b)) i
  A∨B→A0□ (push a i) = inl north

  Iso-A0□-⋁ : Iso (A0□ whitehead3x3) A∨B
  fun Iso-A0□-⋁ = A0□→A∨B
  inv Iso-A0□-⋁ = A∨B→A0□
  rightInv Iso-A0□-⋁ (inl x) = refl
  rightInv Iso-A0□-⋁ (inr north) = push tt
  rightInv Iso-A0□-⋁ (inr south) = push tt ∙ λ i → inr (merid b₀ i)
  rightInv Iso-A0□-⋁ (inr (merid a i)) j = lem j i
    where
    lem : PathP (λ i → push tt i ≡ (push tt ∙ (λ i → inr (merid b₀ i))) i)
              (cong A0□→A∨B (cong A∨B→A0□ λ i → inr (merid a i)))
              (λ i → inr (merid a i))
    lem = (cong-∙ A0□→A∨B (push b₀) (sym (push a))
      ∙ cong₂ _∙_ (cong (push tt ∙_)
                  (λ j i → inr (rCancel (merid b₀) j (~ i)))
                 ∙ sym (rUnit (push tt)))
                  (symDistr (push tt) (λ i → inr (σB a (~ i)))))
      ◁ λ i j → hcomp (λ k →
                  λ { (i = i0) → compPath-filler' (push tt)
                                 (compPath-filler (λ i → inr (σB a i))
                                                  (sym (push tt)) k) k j
                    ; (i = i1) → inr (merid a j)
                    ; (j = i0) → push tt (i ∨ ~ k)
                    ; (j = i1) → compPath-filler' (push tt)
                                                  (λ i → inr (merid b₀ i)) k i})
                        (inr (compPath-filler (merid a)
                                              (sym (merid b₀)) (~ i) j))

  rightInv Iso-A0□-⋁ (push a i) j = push tt (i ∧ j)
  leftInv Iso-A0□-⋁ (inl x) = refl
  leftInv Iso-A0□-⋁ (inr tt) = push b₀
  leftInv Iso-A0□-⋁ (push b i) j = help j i
    where
    help : PathP (λ i → inl north ≡ push b₀ i)
                 (cong A∨B→A0□ (cong A0□→A∨B (push b)))
                 (push b)
    help = (cong-∙ A∨B→A0□ (push tt) (λ i → inr (σB b (~ i)))
         ∙ (λ i → lUnit (sym (cong-∙ (A∨B→A0□ ∘ inr)
                               (merid b) (sym (merid b₀)) i)) (~ i))
         ∙ cong sym (cong ((push b₀ ∙ sym (push b)) ∙_)
                      (cong sym (rCancel (push b₀))))
         ∙ cong sym (sym (rUnit (push b₀ ∙ sym (push b)))))
         ◁ λ i j → compPath-filler' (push b₀) (sym (push b)) (~ i) (~ j)

  Iso-A2□-join : Iso (A2□ whitehead3x3) (join A B)
  fun Iso-A2□-join (inl x) = inr x
  fun Iso-A2□-join (inr x) = inl x
  fun Iso-A2□-join (push (a , b) i) = push a b (~ i)
  inv Iso-A2□-join (inl x) = inr x
  inv Iso-A2□-join (inr x) = inl x
  inv Iso-A2□-join (push a b i) = push (a , b) (~ i)
  rightInv Iso-A2□-join (inl x) = refl
  rightInv Iso-A2□-join (inr x) = refl
  rightInv Iso-A2□-join (push a b i) = refl
  leftInv Iso-A2□-join (inl x) = refl
  leftInv Iso-A2□-join (inr x) = refl
  leftInv Iso-A2□-join (push a i) = refl

  isContrA4□ : isContr (A4□ whitehead3x3)
  fst isContrA4□ = inr tt
  snd isContrA4□ (inl x) = sym (push x)
  snd isContrA4□ (inr x) = refl
  snd isContrA4□ (push a i) j = push a (i ∨ ~ j)

  A4□≃Unit : A4□ whitehead3x3 ≃ Unit
  A4□≃Unit = isContr→≃Unit isContrA4□

  Iso-A□0-Susp : Iso (A□0 whitehead3x3) (Susp A)
  fun Iso-A□0-Susp (inl x) = x
  fun Iso-A□0-Susp (inr x) = north
  fun Iso-A□0-Susp (push a i) = merid a₀ (~ i)
  inv Iso-A□0-Susp x = inl x
  rightInv Iso-A□0-Susp x = refl
  leftInv Iso-A□0-Susp (inl x) = refl
  leftInv Iso-A□0-Susp (inr x) = (λ i → inl (merid a₀ i)) ∙ push x
  leftInv Iso-A□0-Susp (push a i) j =
    hcomp (λ k → λ { (i = i0) → inl (merid a₀ (k ∨ j))
                    ; (i = i1) → compPath-filler
                                   (λ i₁ → inl (merid a₀ i₁))
                                   (push (idfun B a)) k j
                    ; (j = i0) → inl (merid a₀ (~ i ∧ k))
                    ; (j = i1) → push a (i ∧ k)})
          (inl (merid a₀ j))

  Iso-A□2-Susp× : Iso (A□2 whitehead3x3) (Susp A × B)
  fun Iso-A□2-Susp× (inl x) = north , x
  fun Iso-A□2-Susp× (inr x) = south , x
  fun Iso-A□2-Susp× (push a i) = merid (fst a) i , (snd a)
  inv Iso-A□2-Susp× (north , y) = inl y
  inv Iso-A□2-Susp× (south , y) = inr y
  inv Iso-A□2-Susp× (merid a i , y) = push (a , y) i
  rightInv Iso-A□2-Susp× (north , snd₁) = refl
  rightInv Iso-A□2-Susp× (south , snd₁) = refl
  rightInv Iso-A□2-Susp× (merid a i , snd₁) = refl
  leftInv Iso-A□2-Susp× (inl x) = refl
  leftInv Iso-A□2-Susp× (inr x) = refl
  leftInv Iso-A□2-Susp× (push a i) = refl

  Iso-A□4-Susp : Iso (A□4 whitehead3x3) (Susp A)
  fun Iso-A□4-Susp (inl x) = north
  fun Iso-A□4-Susp (inr x) = south
  fun Iso-A□4-Susp (push a i) = merid a i
  inv Iso-A□4-Susp north = inl tt
  inv Iso-A□4-Susp south = inr tt
  inv Iso-A□4-Susp (merid a i) = push a i
  rightInv Iso-A□4-Susp north = refl
  rightInv Iso-A□4-Susp south = refl
  rightInv Iso-A□4-Susp (merid a i) = refl
  leftInv Iso-A□4-Susp (inl x) = refl
  leftInv Iso-A□4-Susp (inr x) = refl
  leftInv Iso-A□4-Susp (push a i) = refl

  Iso-PushSusp×-Susp×Susp :
    Iso (Pushout {A = Susp A × B} fst fst) (Susp A × Susp B)
  Iso-PushSusp×-Susp×Susp = theIso
    where
    F : Pushout {A = Susp A × B} fst fst
     → Susp A × Susp B
    F (inl x) = x , north
    F (inr x) = x , north
    F (push (x , b) i) = x , σB b i

    G : Susp A × Susp B → Pushout {A = Susp A × B} fst fst
    G (a , north) = inl a
    G (a , south) = inr a
    G (a , merid b i) = push (a , b) i

    retr : retract F G
    retr (inl x) = refl
    retr (inr x) = push (x , b₀)
    retr (push (a , b) i) j = help j i
      where
      help : PathP (λ i → Path (Pushout fst fst) (inl a) (push (a , b₀) i))
                   (cong G (λ i → a , σB b i))
                   (push (a , b))
      help = cong-∙ (λ x → G (a , x)) (merid b) (sym (merid b₀))
                  ◁ λ i j → compPath-filler
                               (push (a , b))
                               (sym (push (a , b₀)))
                               (~ i) j

    theIso : Iso (Pushout fst fst) (Susp A × Susp B)
    fun theIso = F
    inv theIso = G
    rightInv theIso (a , north) = refl
    rightInv theIso (a , south) = ΣPathP (refl , merid b₀)
    rightInv theIso (a , merid b i) j =
      a , compPath-filler (merid b) (sym (merid b₀)) (~ j) i
    leftInv theIso = retr

  Iso-A□○-PushSusp× :
    Iso (A□○ whitehead3x3) (Pushout {A = Susp A × B} fst fst)
  Iso-A□○-PushSusp× =
    pushoutIso _ _ fst fst
      (isoToEquiv Iso-A□2-Susp×)
      (isoToEquiv Iso-A□0-Susp)
      (isoToEquiv Iso-A□4-Susp)
      (funExt (λ { (inl x) → refl
                 ; (inr x) → merid a₀
                 ; (push a i) j → help₁ a j i}))
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push a i) j
                  → fun Iso-A□4-Susp (rUnit (push (fst a)) (~ j) i)})
    where
    help₁ : (a : A × B)
      → PathP (λ i → north ≡ merid a₀ i)
               (cong (fun Iso-A□0-Susp)
                 (cong (f□1 whitehead3x3) (push a)))
               (merid (fst a))
    help₁ a =
        (cong-∙∙ (fun Iso-A□0-Susp)
                 (λ i → inl (merid (fst a) i))
                 (push (snd a))
                 refl)
      ◁ (λ i j → hcomp (λ k → λ {(i = i1) → merid (fst a) (j ∨ ~ k)
                                 ; (j = i0) → merid (fst a) (~ k)
                                 ; (j = i1) → merid a₀ i})
                        (merid a₀ (i ∨ ~ j)))

  Iso-A□○-Susp×Susp : Iso (A□○ whitehead3x3) (Susp A × Susp B)
  Iso-A□○-Susp×Susp = compIso Iso-A□○-PushSusp× Iso-PushSusp×-Susp×Susp

  Iso-A○□-cofibW : Iso (A○□ whitehead3x3) cofibW
  Iso-A○□-cofibW =
    pushoutIso _ _
      W (λ _ → tt)
      (isoToEquiv Iso-A2□-join) (isoToEquiv Iso-A0□-⋁)
      A4□≃Unit
      (funExt lem)
      λ _ _ → tt
    where
    lem : (x : A2□ whitehead3x3)
      → A0□→A∨B (f1□ whitehead3x3 x) ≡ W (fun Iso-A2□-join x)
    lem (inl x) = (λ i → inl (merid a₀ (~ i)))
    lem (inr x) = refl
    lem (push (a , b) i) j = help j i
      where
      help : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
                                ((inl (merid a₀ (~ i))))
                                (inr north))
                   (cong A0□→A∨B (cong (f1□ whitehead3x3) (push (a , b))))
                   (cong W (cong (fun Iso-A2□-join) (push (a , b))))
      help = (cong-∙∙ A0□→A∨B (λ i → inl (merid a (~ i))) (push b) refl
            ∙ λ j → (λ i₂ → inl (merid a (~ i₂)))
                   ∙∙ compPath-filler (push tt) (λ i → inr (σB b (~ i))) (~ j)
                   ∙∙ λ i → inr (σB b (~ i ∧ j)))
           ◁ (λ j → (λ i → inl (sym (compPath-filler
                                       (merid a) (sym (merid a₀)) j) i))
                   ∙∙ push tt
                   ∙∙ λ i → inr (σB b (~ i)))

  Iso₁-Susp×Susp-cofibW : Iso (Susp A × Susp B) cofibW
  Iso₁-Susp×Susp-cofibW =
    compIso (invIso Iso-A□○-Susp×Susp)
            (compIso (3x3-Iso whitehead3x3) Iso-A○□-cofibW)

  -- Main iso
  Iso-Susp×Susp-cofibJoinTo⋁ : Iso (Susp A × Susp B) cofibW
  Iso-Susp×Susp-cofibJoinTo⋁ =
    compIso (Σ-cong-iso-snd (λ _ → invSuspIso))
            Iso₁-Susp×Susp-cofibW

  -- The induced function A ∨ B → Susp A × Susp B satisfies
  -- the following identity
  Susp×Susp→cofibW≡ : Path (A∨B → Susp A × Susp B)
                      (Iso.inv Iso-Susp×Susp-cofibJoinTo⋁ ∘ inl)
                      ⋁↪
  Susp×Susp→cofibW≡ =
    funExt λ { (inl x) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr north) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr south) → refl
             ; (inr (merid a i)) j → lem₂ a j i
             ; (push a i) j → north , (merid b₀ (~ j))}
    where
    f₁ = fun Iso-PushSusp×-Susp×Susp
    f₂ = fun Iso-A□○-PushSusp×
    f₃ = backward-l whitehead3x3
    f₄ = fun (Σ-cong-iso-snd (λ _ → invSuspIso))

    lem : (b : B)
      → cong (f₁ ∘ f₂ ∘ f₃) (push b)
      ≡ (λ i → north , σB b i)
    lem b = cong (cong f₁) (sym (rUnit (push (north , b))))

    lem₂ : (a : B)
      → PathP (λ i → (north , merid b₀ (~ i)) ≡ (north , south))
               (cong (f₄ ∘ f₁ ∘ f₂ ∘ f₃ ∘ A∨B→A0□ ∘ inr) (merid a))
               λ i → north , merid a i
    lem₂ a =
         cong (cong f₄) (cong-∙ (f₁ ∘ f₂ ∘ f₃) (push b₀) (sym (push a))
      ∙∙ cong₂ _∙_ (lem b₀ ∙ (λ j i → north , rCancel (merid b₀) j i))
                   (cong sym (lem a))
      ∙∙ sym (lUnit (λ i₁ → north , σB a (~ i₁))))
       ∙ (λ i j → north , cong-∙ invSusp (merid a) (sym (merid b₀)) i (~ j) )
        ◁ λ i j → north , compPath-filler (sym (merid a)) (merid b₀) (~ i) (~ j)

