{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Join

open import Cubical.Homotopy.WhiteheadProducts.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base

open Iso
open 3x3-span

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
              ∙∙ compPath-filler' (cong (fst g) (IsoSucSphereSusp∙ m)) (snd g) (~ i)
               ∙ sym (compPath-filler' (cong (fst f) (IsoSucSphereSusp∙ n)) (snd f) (~ i))
              ∙∙ cong (fst f)
                      ((λ j → IsoSucSphereSusp∙ n (i ∨ j))
                      ∙∙ σS a
                      ∙∙ sym (IsoSucSphereSusp∙ n))))
       ◁ compPathR→PathP∙∙
           ( ∙∙Distr∙
          ∙ cong₂ _∙_ (cong₂ _∙_ (cong (cong (fst g)) (sym (compPath≡compPath' _ _)))
                                 refl)
                      refl
          ∙ cong₂ _∙_ (cong (_∙ snd g) (cong-∙ (fst g) (IsoSucSphereSusp∙ m) (σS b))
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
               ∙∙ sym (compPath-filler (cong (fst f) (IsoSucSphereSusp∙ n)) (snd f) i))

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


open import Cubical.Data.Nat.Order

open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base hiding (·wh)
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Properties
open import Cubical.Homotopy.Group.Join
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Bool hiding (_≤_)
invSphere∙ : {k : ℕ} → invSphere (ptSn (suc k)) ≡ ptSn (suc k)
invSphere∙ {k = zero} = refl
invSphere∙ {k = suc k} = sym (merid (ptSn (suc k)))

-S^pt : {k : ℕ} (n : ℕ) → -S^ {k = suc k} n (ptSn (suc k)) ≡ ptSn (suc k)
-S^pt {k = k} zero = refl
-S^pt {k = k} (suc n) = cong invSphere (-S^pt n) ∙ invSphere∙

-S^∙ : {k : ℕ} (n : ℕ) → S₊∙ (suc k) →∙ S₊∙ (suc k)
-S^∙ n .fst = -S^ n
-S^∙ n .snd = -S^pt n

-S^∙+1 : {k : ℕ} (n : ℕ)
  → (-S^∙ {k = k} 1 ∘∙ -S^∙ {k = k} (suc n)) ≡ -S^∙ {k = k} n
-S^∙+1 {k = k} n i .fst x = invSphere² _ (-S^ n x) i
-S^∙+1 {k = k} n i .snd j =
  hcomp (λ r →
      λ{(i = i1) → invSphere² (suc k) (-S^pt n j) r
      ; (j = i0) → invSphere² (suc k) (-S^ n (S₊∙ (suc k) .snd)) (i ∧ r)
      ; (j = i1) → lem k i r
      })
      (-S^ 1 (compPath-filler (λ i₁ → invSphere (-S^pt n i₁)) invSphere∙ (~ i) j))
  where
  lem : (k : ℕ)
    → Square (refl ∙ invSphere∙)
             (invSphere² (suc k) (ptSn (suc k)))
             (cong invSphere (sym (invSphere∙ {k = k}))) refl
  lem zero = sym (lUnit refl)
  lem (suc k) = sym (lUnit _) ◁ λ i j → merid (ptSn (suc k)) (~ i ∧ ~ j)


suspFun∙Comp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (g : B → C) (f : A → B) → suspFun∙ (g ∘ f) ≡ (suspFun∙ g ∘∙ suspFun∙ f)
suspFun∙Comp f g = ΣPathP ((suspFunComp f g) , rUnit refl)

suspFun∙idfun : ∀ {ℓ} {A : Type ℓ}
  → suspFun∙ (idfun A) ≡ idfun∙ _
suspFun∙idfun = ΣPathP (suspFunIdFun , refl)

private
  -S^∙suspFun₁ : {k : ℕ} → -S^∙ {k = suc k} 1 ≡ suspFun∙ (-S^ {k = suc k} 1)
  -S^∙suspFun₁ {k = k} =
    ΣPathP ((funExt λ { north → sym (merid (ptSn (suc k)))
                      ; south → merid (ptSn (suc k))
                      ; (merid a i) k → lem a k i})
                      , (sym (lUnit _)
                      ◁ λ i j → merid (ptSn (suc k)) (~ j ∧ ~ i)))
    where
    lem : (a : S₊ (suc k))
      → Square (sym (merid a)) (merid (invSphere a))
                (sym (merid (ptSn (suc k)))) (merid (ptSn (suc k)))
    lem a =
       (λ i → compPath-filler
                 (sym (compPath-filler (merid a)
                        (sym (merid (ptSn (suc k)))) i))
                 (merid (ptSn (suc k))) i)
      ▷ (refl
      ∙ cong (_∙ merid (ptSn (suc k))) (sym (σ-invSphere _ a))
      ∙ sym (assoc _ _ _)
      ∙ cong₂ _∙_ refl (lCancel _)
      ∙ sym (rUnit _))

-S^∙suspFun : {k : ℕ} (n : ℕ) → -S^∙ {k = suc k} n ≡ suspFun∙ (-S^ {k = suc k} n)
-S^∙suspFun zero = ΣPathP (sym suspFunIdFun , refl)
-S^∙suspFun (suc n) =
    ΣPathP (refl , cong₂ _∙_ refl (lUnit _))
  ∙ cong₂ _∘∙_ -S^∙suspFun₁ (-S^∙suspFun n)
  ∙ sym (suspFun∙Comp (-S^ 1) (-S^ n))

-π^ : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ) → π' (suc k) A → π' (suc k) A
-π^ {k = k} n = iter n (-π' k)

-π^≡iter-Π : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ)
  → (x : π' (suc k) A) → -π^ n x ≡ ST.map (iter n -Π) x
-π^≡iter-Π {k = k} zero = ST.elim (λ _ → isSetPathImplicit) λ _ → refl
-π^≡iter-Π {k = k} (suc n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong (-π^ 1) (-π^≡iter-Π {k = k} n ∣ f ∣₂)

open import Cubical.HITs.S1 hiding (_·_)

-Π≡∘-S : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (f : S₊∙ (suc k) →∙ A)
  → -Π f ≡ (f ∘∙ (invSphere , invSphere∙))
-Π≡∘-S {k = zero} {A} f =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) → refl}))
        , lUnit (snd f))
-Π≡∘-S {k = suc k} {A} f =
  ΣPathP ((funExt (λ { north → cong (fst f) (merid (ptSn (suc k)))
                     ; south → refl
                     ; (merid a i) j
                  → fst f (compPath-filler (merid a)
                            (sym (merid (ptSn (suc k)))) (~ j) (~ i))}))
        , (compPath-filler'
             (cong (fst f) (sym (merid (ptSn (suc k)))))
             (snd f)))

iter-Π≡∘-S^ : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ) (f : S₊∙ (suc k) →∙ A)
  → iter n -Π f ≡ (f ∘∙ (-S^ n , -S^pt n))
iter-Π≡∘-S^ {k = k} {A} zero f = ΣPathP (refl , lUnit (snd f))
iter-Π≡∘-S^ {k = k} {A} (suc n) f =
  cong -Π (iter-Π≡∘-S^ {k = k} {A} n f)
  ∙ -Π≡∘-S (f ∘∙ (-S^ n , -S^pt n))
  ∙ ∘∙-assoc f (-S^ n , -S^pt n) (invSphere , invSphere∙) -- 
  ∙ cong (f ∘∙_)
    (ΣPathP ((funExt (λ x → sym (invSphere-S^ n x)))
           , (lem k n)))
  where
  fl : (k : ℕ) (n : ℕ)
    → Σ[ p ∈ invSphere (invSphere (ptSn (suc k))) ≡ ptSn (suc k) ]
    ((Square (cong invSphere (sym (invSphere∙ {k = k})) )
            refl invSphere∙ p)
    × Square (cong (invSphere ∘ invSphere) (-S^pt n))
             (cong invSphere (cong invSphere (-S^pt n) ∙ invSphere∙) ∙ invSphere∙)
             refl
             p)
  fl zero n .fst = refl
  fl (suc k) n .fst = refl
  fl zero n .snd = refl
    , (cong (congS invLooper) (rUnit (cong invLooper (-S^pt n))) ∙ rUnit _)
  fl (suc k) n .snd .fst i j = merid (ptSn (suc k)) (~ i ∧ ~ j)
  fl (suc k) n .snd .snd i j =
    hcomp (λ r → λ {(i = i0) → invSusp (invSusp (-S^pt n j))
                   ; (j = i0) → invSusp (invSusp (iter n invSusp north))
                   ; (j = i1) → merid (ptSn (suc k)) (~ r ∧ i)})
           (invSusp (compPath-filler (cong invSusp (-S^pt n))
                      (sym (merid (ptSn (suc k)))) i j))

  lem : (k : ℕ) (n : ℕ)
    → Square (cong (-S^ n) (invSphere∙ {k = k}) ∙ -S^pt n)
              (-S^pt (suc n))
              (sym (invSphere-S^ n (ptSn (suc k)))) refl
  lem k zero = sym (rUnit _) ∙ lUnit _
  lem k (suc n) i j =
    hcomp (λ r → λ {(i = i0) → (cong (-S^ (suc n)) (invSphere∙ {k = k})
                              ∙ compPath-filler (cong invSphere (-S^pt n))
                                                      invSphere∙ r) j
                   ; (i = i1) → fl k n .snd .snd r j
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → fl k n .snd .fst r i
                   })
     (hcomp (λ r → λ {(i = i0) → cong-∙ invSphere
                                         (cong (-S^ n) (invSphere∙ {k = k}))
                                         (-S^pt n) r j
                   ; (i = i1) → invSphere (doubleCompPath-filler refl
                                  (cong invSphere (-S^pt n)) invSphere∙ (~ r) j)
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → invSphere (invSphere∙ (~ r ∨ ~ i))})
          (invSphere (lem k n i j)))

-- isEven' isOdd' : ℕ → Type
-- isEven' n = Σ[ k ∈ ℕ ] n ≡ 2 · k
-- isOdd' n = Σ[ k ∈ ℕ ] n ≡ (2 · k + 1)

-- isEvenT→isEven' : (n : ℕ) → isEvenT n → isEven' n
-- isEvenT→isEven' zero p = 0 , refl
-- isEvenT→isEven' (suc (suc n)) p =
--    (suc (fst (isEvenT→isEven' n p)))
--   , (cong (suc ∘ suc) ( snd (isEvenT→isEven' n p))
--   ∙ cong suc (sym (+-suc (isEvenT→isEven' n p .fst)
--                   (1 · isEvenT→isEven' n p .fst))))

-- open import Cubical.Data.Empty as ⊥
-- isEven'→isEvenT : (n : ℕ) → isEven' n → isEvenT n
-- isEven'→isEvenT zero (x , p) = tt
-- isEven'→isEvenT (suc zero) (zero , p) = snotz p
-- isEven'→isEvenT (suc zero) (suc x , p) =
--   snotz (sym (+-suc x (x + zero)) ∙ sym (cong predℕ p))
-- isEven'→isEvenT (suc (suc n)) (zero , p) = {!snotz ?!}
-- isEven'→isEvenT (suc (suc n)) (suc x , p) = {!p!}
-- isEven'→isEvenT n ({!!} , {!!})
{-
isEvenT→isEven' zero p = 0 , refl
isEvenT→isEven' (suc (suc n)) p =
   (suc (fst (isEvenT→isEven' n p)))
  , (cong (suc ∘ suc) ( snd (isEvenT→isEven' n p))
  ∙ cong suc (sym (+-suc (isEvenT→isEven' n p .fst)
                  (1 · isEvenT→isEven' n p .fst))))
-}
-- isOddT→isOdd' : (n : ℕ) → isOddT n → isOdd' n
-- isOddT→isOdd' (suc n) p .fst = isEvenT→isEven' n p .fst
-- isOddT→isOdd' (suc n) p .snd =
--   cong suc (isEvenT→isEven' n p .snd)
--   ∙ +-comm 1 (2 · isEvenT→isEven' n p .fst)

-- evenOrOdd' : (n : ℕ) → isEven' n ⊎ isOdd' n
-- evenOrOdd' n = {!!}

open import Cubical.Data.Nat.IsEven

-S^-even : {k : ℕ} (n : ℕ) → isEvenT n → (x : S₊ (suc k)) → -S^ n x ≡ x
-S^-even zero p x = refl
-S^-even (suc (suc n)) p x =
  cong (invSphere ∘ invSphere) (-S^-even n p x)
  ∙ invSphere² _ x

-S^∙-even : {k : ℕ} (n : ℕ) → isEvenT n → -S^∙ {k = k} n ≡ idfun∙ (S₊∙ (suc k))
-S^∙-even {k = k} n p  = ΣPathP ((funExt (-S^-even n p)) , lem k n p)
  where
  lem : (k n : ℕ) (p : _) → PathP (λ i → -S^-even n p (ptSn (suc k)) i ≡ ptSn (suc k))
                                   (-S^pt n) (λ _ → ptSn (suc k))
  lem k zero p = refl
  lem zero (suc (suc n)) p =
    (sym (rUnit _) ∙ cong (congS invSphere) (sym (rUnit _)))
    ◁ flipSquare (sym (rUnit _)
    ◁ λ i j → invLooper (invLooper (lem zero n p j i)))
  lem (suc k) (suc (suc n)) p =
    (cong₂ _∙_ (cong-∙ invSphere (cong invSphere (-S^pt n)) invSphere∙) refl
    ∙ sym (assoc _ _ _)
    ∙ cong₂ _∙_ refl (rCancel _)
    ∙ sym (rUnit _))
    ◁ flipSquare (sym (rUnit _) ◁ λ i j → invSphere (invSphere (lem (suc k) n p j i)))

-S^∙-odd : {k : ℕ} (n : ℕ) → isOddT n → -S^∙ {k = k} n ≡ (invSphere , invSphere∙)
-S^∙-odd {k = k} (suc n) o =
  cong ((invSphere , invSphere∙) ∘∙_) (-S^∙-even {k = k} n o) ∙ ∘∙-idˡ _

-S^-odd : {k : ℕ} (n : ℕ) → isOddT n → (x : S₊ (suc k)) → -S^ n x ≡ invSphere x
-S^-odd (suc zero) p x = refl
-S^-odd (suc (suc (suc n))) p x =
  cong (invSphere ∘ invSphere) (-S^-odd (suc n) p x)
  ∙ invSphere² _ (invSphere x)

even+even≡even : (n m : ℕ) → isEvenT n → isEvenT m → isEvenT (n + m)
even+even≡even zero m p q = q
even+even≡even (suc (suc n)) m p q = even+even≡even n m p q

even+odd≡odd : (n m : ℕ) → isEvenT n → isOddT m → isOddT (n + m)
even+odd≡odd zero m p q = q
even+odd≡odd (suc (suc n)) m p q = even+odd≡odd n m p q

odd+even≡odd : (n m : ℕ) → isOddT n → isEvenT m → isOddT (n + m)
odd+even≡odd n m p q = subst isOddT (+-comm m n) (even+odd≡odd m n q p)

odd+odd≡even : (n m : ℕ) → isOddT n → isOddT m → isEvenT (n + m)
odd+odd≡even (suc n) (suc m) p q = subst isEvenT (cong suc (sym (+-suc n m)))
  (even+even≡even n m p q)

isEven·2 : (n : ℕ) → isEvenT (n + n)
isEven·2 zero = tt
isEven·2 (suc n) = subst isEvenT (cong suc (+-comm (suc n) n)) (isEven·2 n)

even·x≡even : (n m : ℕ) → isEvenT n → isEvenT (n · m)
even·x≡even zero m p = tt
even·x≡even (suc (suc n)) m p =
  subst isEvenT (sym (+-assoc m m (n · m)))
    (even+even≡even (m + m) (n · m) (isEven·2 m) (even·x≡even n m p))

x·even≡even : (n m : ℕ) → isEvenT m → isEvenT (n · m)
x·even≡even n m p = subst isEvenT (·-comm m n) (even·x≡even m n p)

odd·odd≡odd : (n m : ℕ) → isOddT n → isOddT m → isOddT (n · m)
odd·odd≡odd (suc n) (suc m) p q =
  subst isOddT t (even+even≡even m _ q (even+even≡even n _ p (even·x≡even n m p)))
  where
  t : suc (m + (n + n · m)) ≡ suc (m + n · suc m)
  t = cong suc (cong (m +_) (cong (n +_) (·-comm n m) ∙ ·-comm (suc m) n))

-S^-commId : {k : ℕ}
  (n m : ℕ) → -S^∙ {k = k} (n · m)
             ≡ -S^∙ {k = k} (suc (suc n · suc m))
-S^-commId {k = k} n m with (evenOrOdd n) | (evenOrOdd m)
... | inl evn | inl evm =
    -S^∙-even _ (even·x≡even n m evn)
  ∙ sym (-S^∙-even (suc (suc (m + n · suc m))) {!
         (even+even≡even 2 (m + n · suc m) tt
          (even+even≡even m (n · suc m) evm (even·x≡even n (suc m) evn)))!})
... | inl evn | inr odm =
  -S^∙-even _ (even·x≡even n m evn)
  ∙ sym {!!}
... | inr odn | inl evm = {!!}
... | inr odn | inr odm = {!!}

-π^-commId : ∀ {ℓ} {X : Pointed ℓ} {k : ℕ}
  (n m : ℕ) (f : π' (suc k) X)
    → -π^ (suc n · suc m) f ≡ {!-π^ (n · m)!}
-π^-commId = {!!}
-- iter-Π≡∘-S^

-- [_∣_]π*-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
--        (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
--        → [ f ∣ g ]π* ≡ fun (π*SwapIso (suc m) (suc n) X) [ g ∣ f ]π*
-- [_∣_]π*-comm {n = n} {m = m} = elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
--   λ f g → cong ∣_∣₂
--     (WhiteheadProdComm'
--         (S₊∙ (suc n)) (S₊∙ n)
--           (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
--         (S₊∙ (suc m)) (S₊∙ m)
--           (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g
--     ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f ∘∙_)
--        (ΣPathP (refl , sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit _)))))

-- open import Cubical.HITs.Sn.Multiplication
-- open import Cubical.HITs.S1.Base hiding (_·_)

-- cong-invsphere-σS : {k : ℕ} (x : S₊ (suc k))
--   → Square (cong invSphere (σS x)) (σS (invSphere x))
--             invSphere∙ invSphere∙
-- cong-invsphere-σS {k = k} x =
--   (cong-∙ invSusp (merid x) (sym (merid (ptSn (suc k))))
--   ∙ refl)
--   ◁ ((λ i → (λ j → merid (ptSn (suc k)) (~ i ∨ j))
--           ∙∙ sym (merid x)
--           ∙∙ (λ j → merid (ptSn (suc k)) (~ i ∧ j)))
--   ▷ (sym (compPath≡compPath'
--            (merid (ptSn (suc k))) (sym (merid x)))
--   ∙ sym (symDistr (merid x) (sym (merid (ptSn (suc k)))))
--   ∙ sym (σS-S^ 1 x)))

-- cong-S^σ : (n k : ℕ) (a : S₊ (suc n))
--   → Square (σSn (suc n) (-S^ k a))
--             (cong (-S^ k) (σS a))
--             (sym (-S^pt k)) (sym (-S^pt k))
-- cong-S^σ n zero a = refl
-- cong-S^σ n (suc k) a i j =
--   hcomp (λ r → λ{(i = i0) → cong-invsphere-σS (-S^ k a) r j
--                 ; (i = i1) → -S^ (suc k) (σS a j)
--                 ; (j = i0) → compPath-filler (cong invSphere (-S^pt k))
--                                               invSphere∙ r (~ i)
--                 ; (j = i1) → compPath-filler (cong invSphere (-S^pt k))
--                                               invSphere∙ r (~ i)})
--         (invSphere (cong-S^σ n k a i j))

-- join-commFun-sphere→Join : (n m : ℕ) (x : _)
--   → PathP (λ i → S₊ (suc (+-comm n m i)))
--           (join→Sphere n m (join-commFun x))
--           (-S^ (suc (m · n)) (join→Sphere m n x))
-- join-commFun-sphere→Join n m (inl x) =
--     (λ i → ptSn (suc (+-comm n m i)))
--   ▷ sym (-S^pt (suc (m · n)))
-- join-commFun-sphere→Join n m (inr x) =
--   (λ i → ptSn (suc (+-comm n m i)))
--   ▷ sym (-S^pt (suc (m · n)))
-- join-commFun-sphere→Join zero zero (push a b i) j = lem j i
--   where
--   main : (a b : Bool) → sym (σS (b ⌣S a)) ≡ cong (-S^ 1) (σS (a ⌣S b))
--   main false false = refl
--   main false true = refl
--   main true false = refl
--   main true true = refl

--   lem : Square (sym (σS (b ⌣S a))) (cong (-S^ 1) (σS (a ⌣S b)))
--                (refl ∙ (refl ∙ refl)) (refl ∙ (refl ∙ refl))
--   lem = flipSquare (sym (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl))
--     ◁ flipSquare (main a b)
--     ▷ (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl)))

-- join-commFun-sphere→Join zero (suc m) (push a b i) j =
--   comp (λ k → S₊ (suc (+-comm zero (suc m) (j ∧ k))))
--        (λ k →
--       λ{(i = i0) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
--                    ▷ sym (-S^pt (suc (·-comm zero m k)))) j
--       ; (i = i1) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
--                    ▷ sym (-S^pt (suc (·-comm zero m k)))) j
--       ; (j = i0) → σSn (suc m) (b ⌣S a) (~ i)
--       ; (j = i1) → -S^ (suc (·-comm zero m k))
--                       (σS (toPathP {A = λ i → S₊ (+-comm zero (suc m) i)}
--                                    (sym (comm⌣S a b)) k) i)})
--    (hcomp (λ k →
--       λ{(i = i0) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
--       ; (i = i1) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
--       ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
--       ; (j = i1) → cong-S^σ m (suc zero) (b ⌣S a) k i})
--        (σ (S₊∙ (suc m)) (-S^ 1 (b ⌣S a)) i))
--   where
--   n = zero
--   lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
--   lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
--       ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
--       ∙ -S^·2 (m · n) (b ⌣S a)
-- join-commFun-sphere→Join (suc n') m (push a b i) j =
--   comp (λ k → S₊ (suc (+-comm n m (j ∧ k))))
--        (λ k →
--       λ{(i = i0) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
--                   ▷ sym (-S^pt (suc (m · n)))) j
--       ; (i = i1) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
--                   ▷ sym (-S^pt (suc (m · n)))) j
--       ; (j = i0) → σSn (n + m) (b ⌣S a) (~ i)
--       ; (j = i1) → -S^ (suc (m · n))
--                         (σS (toPathP {A = λ i → S₊ (+-comm n m i)}
--                                  (sym (comm⌣S a b)) k) i)})
--    (hcomp (λ k →
--       λ{(i = i0) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
--       ; (i = i1) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
--       ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
--       ; (j = i1) → cong-S^σ (n' + m) (suc (m · n))
--                              (-S^ (n · m) (b ⌣S a)) k i})
--       (σ (S₊∙ (suc (n' + m))) (invSphere (lem (~ j))) i))
--   where
--   n = suc n'
--   lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
--   lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
--       ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
--       ∙ -S^·2 (m · n) (b ⌣S a)

-- -- todo: move elsewhere
-- open import Cubical.Data.Empty as ⊥

-- private
--   -S^σS-lem : (n m : ℕ) (a : S₊ n) (b : S₊ m)
--     → (1 ≤ n + m)
--     → PathP
--       (λ i₁ → -S^∙ {k = +-comm m n (~ i₁)} (suc (m · n)) .snd i₁
--              ≡ -S^∙ (suc (m · n)) .snd i₁)
--       ((cong (-S^ (suc (m · n)))
--              (σS (subst S₊ (+-comm m n) (-S^ (m · n) (b ⌣S a))))))
--       (σS (-S^ (suc (m · n)) (-S^ (m · n) (b ⌣S a))))
--   -S^σS-lem zero zero a b ineq = ⊥.rec (snotz (+-comm 1 (ineq .fst) ∙ snd ineq))
--   -S^σS-lem zero (suc m) a b ineq i j =
--     cong-S^σ _ (suc (m · zero))
--      (transp (λ j → S₊ (+-comm (suc m) zero (j ∧ ~ i)))
--              i (-S^ (suc m · zero) (b ⌣S a))) (~ i) j
--   -S^σS-lem (suc n) zero a b ineq i j =
--     cong-S^σ _ (suc zero)
--      (transp (λ j → S₊ (+-comm zero (suc n) (j ∧ ~ i)))
--              i (b ⌣S a)) (~ i) j
--   -S^σS-lem (suc n) (suc m) a b ineq i j =
--     cong-S^σ _ (suc (suc m · suc n))
--                    (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
--                            i (-S^ (suc m · suc n) (b ⌣S a))) (~ i) j

-- open import Cubical.HITs.Truncation as TR
-- open import Cubical.Homotopy.Connected
-- open import Cubical.Foundations.Transport

-- open import Cubical.HITs.PropositionalTruncation as PT


-- join→Sphere∘join-commFunId : (n m : ℕ) (x : _)
--   → PathP (λ i → S₊ (suc (+-comm m n (~ i))))
--            (-S^ (suc (m · n)) (join→Sphere n m x))
--            (join→Sphere m n (join-commFun x))
-- join→Sphere∘join-commFunId n m (inl x) i = -S^∙ (suc (m · n)) .snd i
-- join→Sphere∘join-commFunId n m (inr x) i = -S^∙ (suc (m · n)) .snd i
-- join→Sphere∘join-commFunId zero zero (push a b i) j =
--   (sym (rUnit refl) ◁  flipSquare (lem a b) ▷ rUnit refl) i j
--   where
--   lem : (a b : Bool) → cong invSphere (σS (a ⌣S b)) ≡ sym (σS (b ⌣S a))
--   lem false false = refl
--   lem false true = refl
--   lem true false = refl
--   lem true true = refl
-- join→Sphere∘join-commFunId (suc n') zero (push a b i) j = lem j i
--   where
--   n = suc n'
--   m = zero
--   lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
--                 (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
--                 (sym (σS (b ⌣S a)))
--                 (λ i → -S^∙ (suc (m · n)) .snd i)
--                 λ i → -S^∙ (suc (m · n)) .snd i
--   lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
--              (comm⌣S a b)
--       ◁ -S^σS-lem n zero a b (n' + zero , +-comm (n' + zero) 1)
--       ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
--                ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
--                                ∙ -S^·2 (m · n) (b ⌣S a)))
--            ∙ σ-invSphere _ (b ⌣S a))
-- join→Sphere∘join-commFunId n (suc m') (push a b i) j = lem j i
--   where
--   m = suc m'
--   lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
--                 (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
--                 (sym (σS (b ⌣S a)))
--                 (λ i → -S^∙ (suc (m · n)) .snd i)
--                 λ i → -S^∙ (suc (m · n)) .snd i
--   lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
--              (comm⌣S a b)
--       ◁ -S^σS-lem n (suc m') a b (n + m' , +-comm (n + m') 1 ∙ sym (+-suc n m'))
--       ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
--                ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
--                                ∙ -S^·2 (m · n) (b ⌣S a)))
--            ∙ σ-invSphere _ (b ⌣S a))

-- [_∣_]π'-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
--        (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
--     → [ f ∣ g ]π'
--       ≡ subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
--               (-π^ (suc (suc m · suc n)) [ g ∣ f ]π')
-- [_∣_]π'-comm {X = X} {n} {m} =
--   PT.rec (isPropΠ2 (λ _ _ → squash₂ _ _)) (λ main →
--   ST.elim2 (λ _ _ → isSetPathImplicit)
--   λ f g → cong ∣_∣₂
--     (cong (λ f → _∘∙_ {A = S₊∙ (suc (suc (n + suc m)))}
--                       f (sphere→Join (suc n) (suc m)
--                        , IsoSphereJoin⁻Pres∙ (suc n) (suc m)))
--                (WhiteheadProdComm' (S₊∙ (suc n)) (S₊∙ n)
--                  (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
--                  (S₊∙ (suc m)) (S₊∙ m)
--                  (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g)
--                ∙ refl)
--             ∙ cong ∣_∣₂ (∘∙-assoc (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f)
--                                    join-commFun∙
--                                    (sphere→Join (suc n) (suc m)
--                                    , (λ _ → inl (ptSn (suc n)))))
--             ∙ sym (fromPathP {A = λ i → π' (suc (+-comm (suc m) (suc n) i)) X}
--                   ((-π^≡iter-Π (suc (suc m · suc n)) [ ∣ g ∣₂ ∣ ∣ f ∣₂ ]π'
--                   ∙ cong ∣_∣₂ (iter-Π≡∘-S^ (suc (suc m · suc n)) [ g ∣ f ])
--                   ∙ cong ∣_∣₂ (∘∙-assoc _ _ _))
--                   ◁ λ i → ∣ [ g ∣ f ]-pre ∘∙ main i ∣₂))) main

--   where
--   main' : (x : _)
--     → PathP (λ i → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
--              (-S^ (suc (suc m · suc n)) (join→Sphere (suc n) (suc m) x))
--              (join→Sphere (suc m) (suc n) (join-commFun x))
--   main' (inl x) i = -S^∙ (suc (suc m · suc n)) .snd i
--   main' (inr x) i = -S^∙ (suc (suc m · suc n)) .snd i
--   main' (push a b i) j = lem j i
--     where
--     lem : SquareP (λ i j → S₊ (suc (+-comm (suc m) (suc n) (~ i))))
--                   (cong (-S^ (suc (suc m · suc n))) (σS (a ⌣S b)))
--                   (sym (σS (b ⌣S a)))
--                   (λ i → -S^∙ (suc (suc m · suc n)) .snd i)
--                   λ i → -S^∙ (suc (suc m · suc n)) .snd i
--     lem = cong (congS (-S^ (suc (suc m · suc n))) ∘ σS)
--                (comm⌣S a b)
--         ◁ (λ i j → cong-S^σ _ (suc (suc m · suc n))
--                      (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
--                              i (-S^ (suc (n + m · suc n)) (b ⌣S a))) (~ i) j)
--         ▷ (cong σS ((λ i → -S^ (suc (suc m · suc n)) (-S^ ((suc m · suc n)) (b ⌣S a)))
--                  ∙ cong invSphere (-S^-comp (suc m · suc n) (suc m · suc n) (b ⌣S a)
--                                  ∙ -S^·2 (suc m · suc n) (b ⌣S a)))
--              ∙ σ-invSphere _ (b ⌣S a))


--   main : ∥ PathP (λ i → S₊∙ (suc (+-comm (suc m) (suc n) i))
--                       →∙ join∙ (S₊∙ (suc m)) (S₊∙ (suc n)))
--                  ((sphere→Join (suc m) (suc n) , refl)
--                  ∘∙ -S^∙ (suc (suc m · suc n)))
--                  (join-commFun∙ ∘∙ (sphere→Join (suc n) (suc m) , refl)) ∥₁
--   main = TR.rec (isProp→isOfHLevelSuc (m + suc n) squash₁)
--     (λ Q → ∣ ΣPathP (fstEq , Q) ∣₁)
--     (isConnectedPathP _
--       (isConnectedPath _
--         (subst (isConnected (suc (suc (suc (m + suc n)))))
--           (isoToPath (invIso (joinSphereIso' (suc m) (suc n))))
--           (sphereConnected (suc (suc m + suc n))) ) _ _) _ _ .fst)
--     where
--     fstEq : PathP _ _ _
--     fstEq = toPathP (funExt (λ s
--       → ((transportRefl _
--         ∙ cong (sphere→Join (suc m) (suc n))
--            (sym (substCommSlice (λ n → S₊ (suc n)) (λ n → S₊ (suc n))
--                                 (λ _ → -S^ (suc (suc m · suc n)))
--                                 (sym (+-comm (suc m) (suc n)))
--                                 (join→Sphere (suc n) (suc m)
--                                   (sphere→Join (suc n) (suc m) s))
--                ∙ cong (-S^ (suc (suc m · suc n)))
--                       (cong (subst (S₊ ∘ suc) (sym (+-comm (suc m) (suc n))))
--                             (Iso.rightInv (IsoSphereJoin (suc n) (suc m)) s)))))
--         ∙ cong (sphere→Join (suc m) (suc n))
--                (fromPathP (main' (sphere→Join (suc n) (suc m) s))))
--         ∙ Iso.leftInv (IsoSphereJoin (suc m) (suc n))
--                        (join-commFun (sphere→Join (suc n) (suc m) s))))

-- open import Cubical.Homotopy.Loopspace
-- open import Cubical.HITs.SmashProduct

-- joinPinchComp : ∀ {ℓ ℓ' ℓ'' ℓA ℓB} {X : Pointed ℓ}
--   {A : Type ℓA} {B : Type ℓB}
--   {A' : Type ℓ'} {B' : Type ℓ''}
--   (g : A → A') (h : B → B') 
--   → (f : A' → B' → Ω X .fst) (x : join A B)
--   → joinPinch X f (join→ g h x)
--    ≡ joinPinch X (λ a b → f (g a) (h b)) x
-- joinPinchComp {X = X} g h f (inl x) = refl
-- joinPinchComp {X = X} g h f (inr x) = refl
-- joinPinchComp {X = X} g h f (push a b i) = refl

-- open import Cubical.Foundations.Pointed.Homogeneous

-- Ω→σ : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
--   (f : Susp∙ (typ A) →∙ B)
--   (g : C →∙ A)
--   → (Ω→ f  ∘∙ (((σ A) , (rCancel _)) ∘∙ g))
--    ≡ (Ω→ (f ∘∙ suspFun∙ (fst g)) ∘∙ (σ C , rCancel _))
-- Ω→σ {A = A} {B} {C} f g =
--   →∙Homogeneous≡ (isHomogeneousPath _ _)
--     (funExt (λ x →
--         cong (Ω→ f .fst)
--           (sym (cong-∙ (suspFun (fst g)) (merid x) (sym (merid (pt C)))
--                       ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (snd g))))))
--   ∙ cong₂ _∘∙_ (cong Ω→ (ΣPathP (refl , lUnit (snd f)))) refl

-- private
--   assocPath : (n m l : ℕ) → _ ≡ _
--   assocPath n m l = (+-assoc (suc m) (suc n) (suc l)
--                           ∙ cong (_+ suc l) (+-comm (suc m) (suc n))
--                           ∙ +-assoc (suc n) (suc m) (suc l) ⁻¹)

-- SphereSmashIso∙ : (n m : ℕ) → Iso.fun (SphereSmashIso n m) (inl tt) ≡ ptSn (n + m)
-- SphereSmashIso∙ zero m = refl
-- SphereSmashIso∙ (suc n) m = refl

-- suspFun∙Cancel : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : Iso A B)
--   → suspFun∙ (fun f) ∘∙ suspFun∙ (inv f)  ≡ id∙ (Susp∙ B)
-- suspFun∙Cancel f = ΣPathP ((funExt (rightInv (congSuspIso f)))
--   , sym (rUnit refl))

-- SphereSmashIso⁻∙ : (n m : ℕ) → Iso.inv (SphereSmashIso n m) (ptSn (n + m)) ≡ inl tt
-- SphereSmashIso⁻∙ n m =
--     sym (cong (Iso.inv (SphereSmashIso n m)) (SphereSmashIso∙ n m))
--   ∙ Iso.leftInv (SphereSmashIso n m) (inl tt)

-- open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base
-- open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Properties
-- -- JacobiΣR
-- open import Cubical.HITs.Join.CoHSpace
-- open import Cubical.Homotopy.HSpace
-- open import Cubical.HITs.SmashProduct.SymmetricMonoidal

-- wh∘∙eq : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--   → {B' : Pointed ℓ'} → (e : B' ≃∙ B)
--   → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
--   → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
--    ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e))
-- wh∘∙eq {A = A} {B} {C} {B'} =
--   Equiv∙J (λ B' e → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
--   → (·whΣ A B' f (g ∘∙ suspFun∙ (fst (fst e))))
--    ≡ (·whΣ A B f g ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e)))
--    λ f g → cong (·whΣ A B f)
--              (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g)
--           ∙ (sym (∘∙-idˡ (·whΣ A B f g)))
--           ∙ cong₂ _∘∙_ refl
--               (sym (ΣPathP (suspFunIdFun , refl))
--               ∙ cong suspFun∙ (sym
--                  (cong fst ⋀→∙-idfun)))

-- wh∘∙eqL : ∀ {ℓ ℓ' ℓ''} {A A' : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--   (e : A' ≃∙ A)
--   (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
--   → ·whΣ A' B (f ∘∙ suspFun∙ (fst (fst e))) g
--   ≡ (·whΣ A B f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ B))
-- wh∘∙eqL {A = A} {B} {C} {B'} =
--   Equiv∙J (λ B e → (f : Susp∙ (typ A) →∙ B')
--       (g : Susp∙ (typ C) →∙ B') →
--       ·whΣ B C (f ∘∙ suspFun∙ (fst (fst e))) g ≡
--       (·whΣ A C f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ C)))
--     λ f g → cong₂ (·whΣ A C) (cong (f ∘∙_) suspFun∙idfun ∙ ∘∙-idˡ f) refl
--            ∙ sym (∘∙-idˡ _)
--            ∙ cong₂ _∘∙_ refl (sym
--               (cong suspFun∙ (cong fst ⋀→∙-idfun)
--               ∙ suspFun∙idfun))


-- open import Cubical.Foundations.Equiv.HalfAdjoint

-- retEqIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
--   (is : Iso A B) (x : _)
--     → retEq (isoToEquiv is) x
--      ≡ ((sym (leftInv is (inv is (fun is x)))
--      ∙ cong (inv is) ((rightInv is (fun is x)))))
--      ∙ leftInv is x
-- retEqIsoToEquiv is x i j =
--   hcomp (λ k → λ {(i = i1) → compPath-filler (sym (leftInv is (inv is (fun is x)))
--                               ∙ cong (inv is) ((rightInv is (fun is x)))) (leftInv is x) k j
--                   ; (j = i0) → (cong (inv is) (sym (rightInv is (fun is x)))
--                               ∙ leftInv is (inv is (fun is x))) (i ∨ k)
--                   ; (j = i1) → lUnit (leftInv is x) (~ i) k
--                   })
--     (lemma j i)
--   where
--   p = sym (symDistr (sym (leftInv is (inv is (fun is x))))
--                         (cong (inv is) (rightInv is (fun is x))))
--   lemma : Square (cong (inv is) (sym (rightInv is (fun is x)))
--                 ∙ leftInv is (inv is (fun is x)))
--           refl refl
--           (sym (leftInv is (inv is (fun is x)))
--          ∙ cong (inv is) ((rightInv is (fun is x))))
--   lemma = p ◁ λ i j → p i1 (~ i ∧ j)

-- []≡·whΣ : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
--   (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
--   →  [ f ∣ g ]
--    ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g
--    ∘∙ suspFun∙ (inv (SphereSmashIso (suc n) (suc m))))
-- []≡·whΣ {X = X} {n} {m} f g =
--     cong₂ _∘∙_ (·whΣ≡·wh _ _ _ _) refl
--   ∙ ∘∙-assoc _ _ _
--   ∙ cong₂ _∘∙_ refl
--     (Iso.inv (congIso (invIso (post∘∙equiv (joinSphereEquiv∙ (suc n) (suc m)))))
--       (-- ∘∙-assoc _ _ _
--        (cong₂ _∘∙_ (cong₂ _∘∙_ refl (ΣPathP
--          (refl , (sym (lem') ∙ lUnit _)))) refl
--        ∙ Iso.leftInv (post∘∙equiv (joinSphereEquiv∙ (suc n) (suc m)))
--           (Join→SuspSmash∙ (S₊∙ (suc n)) (S₊∙ (suc m))))
--      ∙ ΣPathP ((funExt (λ { (inl x) → refl
--                           ; (inr x) → sym (merid (inl tt))
--                           ; (push a b i) j → main a b (~ j) i}))
--                           , rUnit refl)))
--   where
--   main : (a : S₊ (suc n)) (b : S₊ (suc m))
--     → Square (cong (suspFun (inv (SphereSmashIso (suc n) (suc m))))
--                    (σ (S₊∙ (suc n + suc m)) (a ⌣S b)))
--               (merid (inr (a , b)))
--               refl
--               (merid (inl tt))
--   main a b = (cong-∙ (suspFun (inv (SphereSmashIso (suc n) (suc m)))) _ _
--     ∙ cong₂ _∙_ (cong merid (leftInv (SphereSmashIso (suc n) (suc m))
--                                      (inr (a , b))))
--                 (cong (sym ∘ merid) (SphereSmashIso⁻∙ (suc n) (suc m))))
--     ◁ symP (compPath-filler (merid (inr (a , b))) (sym (merid (inl tt))))

--   retEqInvEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) (x : _)
--     → retEq e x ≡ secEq (invEquiv e) x 
--   retEqInvEquiv e x = refl

--   p1 : leftInv (joinSphereIso' (suc n) (suc m)) (inl (ptSn (suc n))) ≡ sym (push (ptSn (suc n)) (ptSn (suc m)))
--   p1 = cong₂ _∙_ (cong (congS (inv (invIso SmashJoinIso))) (sym (rUnit refl))) refl
--      ∙ sym (lUnit _)

--   p2 : rightInv (joinSphereIso' (suc n) (suc m)) north ≡ sym (merid (ptSn (suc n + suc m)))
--   p2 = cong₂ _∙_ (cong (sym ∘ merid) (IdL⌣S {n = suc n} {m = suc m} (ptSn (suc n))))
--        (sym (rUnit refl))
--        ∙ sym (rUnit _)

--   compPath-filler-diag : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
--     → Path (Path A _ _) (λ i → compPath-filler p q (~ i) i) p
--   compPath-filler-diag p q j i = compPath-filler p q (~ i ∧ ~ j) i

--   lem' : retEq (isoToEquiv (IsoSphereJoin (suc n) (suc m))) (inl (ptSn (suc n))) ≡ refl
--   lem' = retEqIsoToEquiv (IsoSphereJoin (suc n) (suc m)) (inl (ptSn (suc n)))
--        ∙ cong₂ _∙_ (cong₂ _∙_ (cong sym (cong₂ _∙_ refl p1 ∙ rCancel _)
--                ∙ refl) (cong-∙ (sphere→Join (suc n) (suc m)) _ _
--                      ∙ cong₂ _∙_ refl (cong (congS (sphere→Join (suc n) (suc m))) p2
--                        ∙ refl) -- cong sym (cong₂ _∙_ refl refl) ∙ {!!})
--                      ∙ refl) ∙ sym (lUnit _)) (cong₂ _∙_ refl p1
--                      ∙ rCancel _)
--        ∙ sym (rUnit _)
--        ∙ cong₂ _∙_
--          (λ j i → sphere→Join (suc n) (suc m)
--                (compPath-filler
--                  (merid (sphereFun↑ _⌣S_ (ptSn (suc n)) (pt (S₊∙ (suc m)))))
--                  (sym (merid (ptSn (suc (n + suc m))))) (~ i ∧ ~ j) i))
--          refl
--        ∙ cong₂ _∙_ (cong₂ _∙_ refl (cong (congS (inv (joinSphereIso' (suc n) (suc m))) ∘ merid) (IdL⌣S {n = suc n} {m = suc m} (ptSn (suc n))))) refl
--        ∙ rCancel _

-- tripleSmasherL≃∙ : {n m l : ℕ}
--   → S₊∙ (suc n + (suc m + suc l))
--   ≃∙ S₊∙ (suc n) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))
-- tripleSmasherL≃∙ {n = n} {m} {l} =
--   compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m + suc l)))
--                         , SphereSmashIso⁻∙ (suc n) (suc m + suc l))
--              (⋀≃ (idEquiv∙ (S₊∙ (suc n)))
--              ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l)))) , (SphereSmashIso⁻∙ (suc m) (suc l)))
--             , refl)

-- tripleSmasherR≃∙ : {n m l : ℕ}
--   → S₊∙ ((suc n + suc m) + suc l)
--   ≃∙ ((S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) ⋀∙ S₊∙ (suc l))
-- tripleSmasherR≃∙ {n = n} {m} {l} =
--   compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n + suc m) (suc l)))
--                         , SphereSmashIso⁻∙ (suc n + suc m) (suc l))
--              (⋀≃ ((isoToEquiv (invIso (SphereSmashIso (suc n) (suc m)))) , (SphereSmashIso⁻∙ (suc n) (suc m)))
--                  (idEquiv∙ (S₊∙ (suc l)))
--             , refl)

-- tripleSmasherL≃∙Id : (n m l : ℕ) (x : _)
--   → PathP (λ i → Susp (S₊ (assocPath n m l (~ i))))
--            (suspFun (-S^ (suc n · suc m)
--                    ∘ invEq (fst (tripleSmasherL≃∙ {n = n} {m} {l}))) x)
--            (suspFun (invEq (fst (tripleSmasherL≃∙ {n = m} {n} {l}))
--                    ∘ inv SmashAssocIso
--                    ∘ (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
--                    ∘ fun SmashAssocIso) x)
-- tripleSmasherL≃∙Id n m l north i = north
-- tripleSmasherL≃∙Id n m l south i = south
-- tripleSmasherL≃∙Id n m l (merid a i) j = lem a j i
--   where
--   lemma : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
--     → PathP (λ i → S₊ (assocPath n m l (~ i)))
--              (-S^ (suc n · suc m) (invEq (fst tripleSmasherL≃∙)
--                (inr (x , inr (y , z)))))
--               (invEq (fst tripleSmasherL≃∙)
--                (inv SmashAssocIso
--                 ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
--                  (fun SmashAssocIso (inr (x , inr (y , z)))))))
--   lemma x y z = transport (λ j →
--     PathP (λ i → S₊ (isSetℕ _ _ p (sym (assocPath n m l)) j i))
--           (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
--           (y ⌣S (x ⌣S z)))
--         help
--     where
--     p = (cong suc (+-assoc n (suc m) (suc l))
--        ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
--        ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

--     help : PathP (λ i → S₊ (p i))
--                  (-S^ (suc n · suc m) (x ⌣S (y ⌣S z)))
--                  (y ⌣S (x ⌣S z))
--     help =
--       compPathP' {B = S₊}
--       (compPathP' {B = S₊}
--         (λ i → -S^ (suc n · suc m) (assoc⌣S x y z i))
--         (λ i → -S^ (suc n · suc m)
--            (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
--                     (sym (comm⌣S x y)) (~ i) ⌣S z))
--       ▷ (cong (-S^ (suc n · suc m))
--                 (⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
--                ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))
--       ∙ -S^² (suc n · suc m) ((y ⌣S x) ⌣S z)))
--       (symP (assoc⌣S y x z))

--   lem : (a : _)
--     → SquareP (λ i j → Susp (S₊ (assocPath n m l (~ i))))
--                (merid ((-S^ (suc n · suc m) ∘ invEq (fst tripleSmasherL≃∙)) a))
--                (merid (invEq (fst tripleSmasherL≃∙)
--                         (inv SmashAssocIso
--                          ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
--                           (fun SmashAssocIso a)))))
--                (λ _ → north)
--                (λ _ → south)
--   lem = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
--     λ x → ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
--       λ y z i → merid (lemma x y z i)

-- ·whΣ-assocer : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
--   (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
--   (h : S₊∙ (2 + l) →∙ X)
--   → [ f ∣ [ g ∣ h ] ]
--    ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) f
--        (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h)
--    ∘∙ suspFun∙ (fst (fst tripleSmasherL≃∙)))
-- ·whΣ-assocer {X = X} {n} {m} {l} f g h =
--     cong₂ [_∣_] refl ([]≡·whΣ {X = X} g h)
--   ∙ []≡·whΣ f _
--   ∙ cong₂ _∘∙_
--       (wh∘∙eq ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l))))
--                                  , (SphereSmashIso⁻∙ (suc m) (suc l))) f
--              (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h))
--       refl
--   ∙ ∘∙-assoc _ _ _
--   ∙ cong₂ _∘∙_ refl (sym (suspFun∙Comp _ _))

-- ·whΣ-assocerR : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
--   (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
--   (h : S₊∙ (2 + l) →∙ X)
--   → [ [ f ∣ g ] ∣ h ]
--    ≡ (·whΣ (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l)) 
--        (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h
--    ∘∙ suspFun∙ ((fst (fst tripleSmasherR≃∙))))
-- ·whΣ-assocerR {X = X} {n} {m} {l} f g h =
--   cong₂ [_∣_]  ([]≡·whΣ {X = X} f g) refl
--   ∙ []≡·whΣ _ _
--   ∙ cong₂ _∘∙_ (wh∘∙eqL (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m)))
--                                  , (SphereSmashIso⁻∙ (suc n) (suc m)))
--                (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h) refl
--   ∙ ∘∙-assoc _ _ _
--   ∙ cong₂ _∘∙_ refl
--     (sym (suspFun∙Comp _ _))

-- ·Susp≡ : ∀ {ℓ ℓ'} (A A' : Pointed ℓ) {X : Pointed ℓ'} (e : A ≃∙ A')
--   → (f g : Susp∙ (typ A) →∙ X)
--   → ·Susp A f g
--    ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
--                (g ∘∙ suspFun∙ (invEq (fst e)))
--     ∘∙ suspFun∙ (fst (fst e)))
-- ·Susp≡ A A' {X} = Equiv∙J (λ A e → (f g : Susp∙ (typ A) →∙ X) →
--       ·Susp A f g
--    ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
--                (g ∘∙ suspFun∙ (invEq (fst e)))
--      ∘∙ suspFun∙ (fst (fst e))))
--  λ f g → sym (cong₂ _∘∙_ (cong₂ (·Susp A')
--    (cong (f ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ f)
--    (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g))
--    (ΣPathP (suspFunIdFun , refl))
--    ∙ ∘∙-idˡ (·Susp A' f g))

-- subst∙ : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
--   → {x y : X} (p : x ≡ y) → A x →∙ A y 
-- subst∙ A p .fst = subst (fst ∘ A) p
-- subst∙ A p .snd i = transp (λ j → fst (A (p (i ∨ j)))) i (pt (A (p i)))

-- subst∙refl : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
--   → {x : X} → subst∙ A (refl {x = x}) ≡ idfun∙ (A x)
-- subst∙refl A {x} = ΣPathP ((funExt transportRefl)
--   , (λ j i → transp (λ t → fst (A x)) (j ∨ i) (pt (A x))))

-- subst∙Id : ∀ {ℓ ℓA ℓB} {X : Type ℓ} (A : X → Pointed ℓA) {B : Pointed ℓB}
--   → {x y : X} (p : x ≡ y) (f : A x →∙ B)
--     → f ∘∙ subst∙ A (sym p) ≡ transport (λ i → A (p i) →∙ B) f 
-- subst∙Id A {B = B} {x = x} =
--   J (λ y p → (f : A x →∙ B)
--             → f ∘∙ subst∙ A (sym p)
--             ≡ transport (λ i → A (p i) →∙ B) f)
--     λ f → (cong₂ _∘∙_ refl (subst∙refl A) ∙ ∘∙-idˡ _)
--          ∙ sym (transportRefl f)

-- private
--   ∘∙preSubstLem : ∀ {ℓ} {X : Type ℓ} (n m : ℕ)
--     (p : n ≡ m)
--     (f : S₊ (suc m) → X)
--     → suspFun∙ (f ∘ subst S₊ (cong suc p))
--     ≡ (suspFun∙ f ∘∙ subst∙ (S₊∙ ∘ suc) (cong suc p))
--   ∘∙preSubstLem n = J> λ f
--     → (cong suspFun∙ (funExt (λ x → cong f (transportRefl x)))
--     ∙ sym (∘∙-idˡ _))
--     ∙ cong₂ _∘∙_ refl (sym (subst∙refl S₊∙))

-- suspFun∙substLem : ∀ {ℓ} {X : Type ℓ} {n m : ℕ}
--   (p : suc n ≡ suc m)
--   (f : S₊ (suc m)  → X)
--   → suspFun∙ (f ∘ subst S₊ p)
--   ≡ suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p
-- suspFun∙substLem p f =
--   cong (λ p → suspFun∙ (f ∘ subst S₊ p)) (isSetℕ _ _ p (cong suc (cong predℕ p)))
--   ∙ ∘∙preSubstLem _ _ _ f
--   ∙ cong (λ p → suspFun∙ f ∘∙ subst∙ (λ x → S₊∙ (suc x)) p) (isSetℕ _ _ (cong suc (cong predℕ p)) p)


-- [_∣_]π'Jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
--   (f : π' (suc (suc n)) X)
--   (g : π' (suc (suc m)) X)
--   (h : π' (suc (suc l)) X)
--   → [ f ∣ [ g ∣ h ]π' ]π'
--    ≡ ·π' _ (subst (λ k → π' k X)
--                   (cong (2 +_) (sym (+-assoc n (suc m) (suc l))))
--                   ([ [ f ∣ g ]π' ∣ h ]π'))
--            (subst (λ k → π' k X)
--                   (cong suc (assocPath n m l))
--                   (-π^ (suc n · suc m) [ g ∣ [ f ∣ h ]π' ]π'))
-- [_∣_]π'Jacobi {X = X} {n} {m} {l} =
--   ST.elim3 (λ _ _ _ → isSetPathImplicit)
--     λ f g h → cong ∣_∣₂
--        (·whΣ-assocer f g h
--       ∙ cong₂ _∘∙_
--         (JacobiΣR' (S₊∙ (suc n)) (S₊∙ n)
--           (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
--           (S₊∙ (suc m)) (S₊∙ m)
--           (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
--           (S₊∙ (suc l)) (S₊∙ l)
--           (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
--           f g h) refl
--       ∙ cong₂ _∘∙_ (·Susp≡ _ _ (invEquiv∙ tripleSmasherL≃∙) _ _) refl
--       ∙ ∘∙-assoc _ _ _
--       ∙ cong₂ _∘∙_ refl
--         (sym (suspFun∙Comp _ _)
--         ∙ cong suspFun∙ (funExt (retEq (fst tripleSmasherL≃∙))) ∙ suspFun∙idfun)
--       ∙ ∘∙-idˡ _
--       ∙ cong₂ (·Susp (S₊∙ (suc (n + suc (m + suc l)))))
--               (sym (sym (subst∙Id (S₊∙ ∘ (2 +_))
--                           (sym (+-assoc n (suc m) (suc l)))
--                           [ [ f ∣ g ] ∣ h ])
--                  ∙ cong₂ _∘∙_ (·whΣ-assocerR f g h) (λ _ → s1)
--                  ∙ ∘∙-assoc _ _ _
--                  ∙ cong₂ _∘∙_ refl (ΣPathP ((funExt λ { north → refl
--                                                       ; south → refl
--                                                       ; (merid a i) j → hoo a j i})
--                                                       , sym (rUnit refl)) ∙ suspFun∙Comp _ _)
--                  ∙ sym (∘∙-assoc _ _ _)))
--               (sym (cong (transport (λ i → S₊∙ (suc (assocPath n m l i)) →∙ X))
--                          (iter-Π≡∘-S^ deg _)
--                   ∙ (sym (subst∙Id (S₊∙ ∘ suc)
--                           (assocPath n m l) _)
--                   ∙ cong₂ _∘∙_ (cong₂ _∘∙_ (·whΣ-assocer g f h)
--                                           (-S^∙suspFun deg)
--                              ∙ ∘∙-assoc _ _ _
--                              ∙ cong₂ _∘∙_ refl
--                                (sym (suspFun∙Comp (fst (fst tripleSmasherL≃∙))
--                                                   (-S^ deg)))) refl)
--                   ∙ ∘∙-assoc _ _ _
--                   ∙ cong₂ _∘∙_ refl
--                     ((cong₂ _∘∙_ refl
--                       refl
--                     ∙ sym (suspFun∙substLem (sym (assocPath n m l))
--                             (fst (fst tripleSmasherL≃∙) ∘ -S^ deg))
--                     ∙ final-lemma)
--                     ∙ suspFun∙Comp _ _)
--                   ∙ sym (∘∙-assoc _ _ _))))
--        ∙ refl
--        ∙ cong₂ (·π' (suc (n + suc (m + suc l)))) refl
--                (cong (subst (λ k → π' k X) (cong suc (assocPath n m l)))
--                      (sym (-π^≡iter-Π deg _)))
--   where
--   deg = suc n · suc m

--   meridLem1 : (a : S₊ (suc (n + suc (m + suc l))))
--     → merid (fst (fst tripleSmasherL≃∙)
--               (-S^ deg (subst S₊ (sym (assocPath n m l)) a)))
--      ≡ merid (inv SmashAssocIso
--               ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
--                (fun SmashAssocIso (fst (fst tripleSmasherL≃∙) a))))
--   meridLem1 a =
--       cong merid (cong (fst (fst tripleSmasherL≃∙)
--                       ∘ -S^ deg
--                       ∘ subst S₊ (sym (assocPath n m l)))
--                  (sym (retEq (fst tripleSmasherL≃∙) a)))
--     ∙ meridLem2 (fst (fst tripleSmasherL≃∙) a)
--     where
--     meridLem2 : (a : _)
--       → merid (fst (fst tripleSmasherL≃∙)
--                 (-S^ deg
--                  (subst S₊ (sym (assocPath n m l))
--                   (invEq (fst tripleSmasherL≃∙) a))))
--        ≡ merid (inv SmashAssocIso
--                 ((⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l)))
--                  (fun SmashAssocIso a))) 
--     meridLem2 =
--       ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
--        λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
--          λ y z → cong merid
--            (refl
--            ∙ cong (fst (fst tripleSmasherL≃∙) ∘ -S^ deg)
--                  (meridLem3 x y z)
--           ∙ cong (fst (fst tripleSmasherL≃∙))
--                  (-S^² deg _)
--           ∙ secEq (fst tripleSmasherL≃∙) (inr (y , inr (x , z))))
--       where
--       p = (cong suc (+-assoc n (suc m) (suc l))
--          ∙ cong (_+ suc l) (sym (+-comm (suc m) (suc n))))
--          ∙ cong suc (sym (+-assoc m (suc n) (suc l)))

--       meridLem3 : (x : S₊ (suc n)) (y : S₊ (suc m)) (z : S₊ (suc l))
--         → subst S₊ (sym (assocPath n m l))
--                     (x ⌣S (y ⌣S z))
--          ≡ -S^ deg (y ⌣S (x ⌣S z))
--       meridLem3 x y z =
--          cong (λ P → subst S₊ P (x ⌣S (y ⌣S z)))
--               (isSetℕ _ _ _ _)
--        ∙ fromPathP
--           (compPathP' {B = S₊}
--           (compPathP' {B = S₊}
--             (λ i → (assoc⌣S x y z i))
--             (λ i → 
--                (toPathP {A = λ i → S₊ (+-comm (suc m) (suc n) i)}
--                        (sym (comm⌣S x y)) (~ i) ⌣S z))
--           ▷ ((⌣Sinvₗ^ (suc m · suc n) (y ⌣S x) z
--                   ∙ λ i → -S^ (·-comm (suc m) (suc n) i) ((y ⌣S x) ⌣S z))))
--          (λ i → -S^ deg (assoc⌣S y x z (~ i))))

--   final-lemma : suspFun∙
--       ((λ x → fst (fst tripleSmasherL≃∙) (-S^ deg x)) ∘
--        subst S₊ (λ i → assocPath n m l (~ i)))
--       ≡
--       suspFun∙
--       ((inv SmashAssocIso ∘
--         (⋀comm→∙ ⋀→ idfun∙ (S₊∙ (suc l))) ∘ fun SmashAssocIso)
--        ∘ invEq (invEquiv (fst tripleSmasherL≃∙)))
--   final-lemma = ΣPathP ((
--     funExt (λ { north → refl
--               ; south → refl
--               ; (merid a i) j → meridLem1 a j i}))
--     , refl)


--   s1 = subst∙ (S₊∙ ∘ (2 +_)) (+-assoc n (suc m) (suc l))
--   s2 = subst∙ (S₊∙ ∘ suc) (sym (assocPath n m l))

--   hoo : (a : S₊ (suc (n + (suc m + suc l))))
--     → cong (suspFun (fst (fst tripleSmasherR≃∙)) ∘ fst s1)
--            (merid a)
--     ≡ merid (fun SmashAssocIso (invEq (fst (invEquiv∙ tripleSmasherL≃∙)) a))
--   hoo a = (λ j i → suspFun (fst (fst tripleSmasherR≃∙))
--                      (transp (λ i → S₊ (suc (suc
--                        (+-assoc n (suc m) (suc l) (i ∨ j))))) j
--                      (merid (transp (λ i → S₊ (suc
--                        (+-assoc n (suc m) (suc l) (i ∧ j))))
--                                     (~ j) a) i)))
--         ∙ cong (merid ∘ fst (fst tripleSmasherR≃∙)
--               ∘ subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l)))
--              (sym (retEq (fst tripleSmasherL≃∙) a))
--         ∙ lem2 (fst (fst tripleSmasherL≃∙) a)
--     where
--     lem2 : (a : _) → merid (fst (fst tripleSmasherR≃∙)
--                              (subst (S₊ ∘ suc) (+-assoc n (suc m) (suc l))
--                                (invEq (fst tripleSmasherL≃∙) a)))
--                     ≡ merid (fun SmashAssocIso a)
--     lem2 = ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
--             λ x → ⋀→HomogeneousPathP refl (isHomogeneousPath _ _)
--               λ y z →
--        cong merid (cong (fst (fst tripleSmasherR≃∙))
--                         (fromPathP (assoc⌣S x y z))
--                 ∙ secEq (fst tripleSmasherR≃∙) (inr (inr (x , y) , z)))

-- jacobiPath₁ : (n m l : ℕ) → {!!} ≡ {!!}
-- jacobiPath₁ = {!!}

-- jacobiPath₂ : {!!}
-- jacobiPath₂ = {!!}

-- [_∣_]π'Jacobi' : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
--   (f : π' (suc (suc n)) X)
--   (g : π' (suc (suc m)) X)
--   (h : π' (suc (suc l)) X)
--   → ·π' (suc n + (suc m + suc l))
--         (-π^ {!!} [ f ∣ [ g ∣ h ]π' ]π')
--       (·π' (suc n + (suc m + suc l))
--         {!-π^ ? !}
--         {!!})
--    ≡ {!!} -- [ f ∣ [ g ∣ h ]π' ]π' 
-- [_∣_]π'Jacobi' = {!!}
