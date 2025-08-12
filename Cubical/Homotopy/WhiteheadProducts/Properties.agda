{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws

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
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Base
-- open import Cubical.Homotopy.WhiteheadProducts.Generalised.Properties

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

[_∣_]π*-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
       → [ f ∣ g ]π* ≡ fun (π*SwapIso (suc m) (suc n) X) [ g ∣ f ]π*
[_∣_]π*-comm {n = n} {m = m} = elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f g → cong ∣_∣₂
    (WhiteheadProdComm'
        (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
        (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m) f g
    ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc n)) g f ∘∙_)
       (ΣPathP (refl , sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit _)))))

open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.S1.Base hiding (_·_)

cong-invsphere-σS : {k : ℕ} (x : S₊ (suc k))
  → Square (cong invSphere (σS x)) (σS (invSphere x))
            invSphere∙ invSphere∙
cong-invsphere-σS {k = k} x =
  (cong-∙ invSusp (merid x) (sym (merid (ptSn (suc k))))
  ∙ refl)
  ◁ ((λ i → (λ j → merid (ptSn (suc k)) (~ i ∨ j))
          ∙∙ sym (merid x)
          ∙∙ (λ j → merid (ptSn (suc k)) (~ i ∧ j)))
  ▷ (sym (compPath≡compPath'
           (merid (ptSn (suc k))) (sym (merid x)))
  ∙ sym (symDistr (merid x) (sym (merid (ptSn (suc k)))))
  ∙ sym (σS-S^ 1 x)))

cong-S^σ : (n k : ℕ) (a : S₊ (suc n))
  → Square (σSn (suc n) (-S^ k a))
            (cong (-S^ k) (σS a))
            (sym (-S^pt k)) (sym (-S^pt k))
cong-S^σ n zero a = refl
cong-S^σ n (suc k) a i j =
  hcomp (λ r → λ{(i = i0) → cong-invsphere-σS (-S^ k a) r j
                ; (i = i1) → -S^ (suc k) (σS a j)
                ; (j = i0) → compPath-filler (cong invSphere (-S^pt k))
                                              invSphere∙ r (~ i)
                ; (j = i1) → compPath-filler (cong invSphere (-S^pt k))
                                              invSphere∙ r (~ i)})
        (invSphere (cong-S^σ n k a i j))

join-commFun-sphere→Join : (n m : ℕ) (x : _)
  → PathP (λ i → S₊ (suc (+-comm n m i)))
          (join→Sphere n m (join-commFun x))
          (-S^ (suc (m · n)) (join→Sphere m n x))
join-commFun-sphere→Join n m (inl x) =
    (λ i → ptSn (suc (+-comm n m i)))
  ▷ sym (-S^pt (suc (m · n)))
join-commFun-sphere→Join n m (inr x) =
  (λ i → ptSn (suc (+-comm n m i)))
  ▷ sym (-S^pt (suc (m · n)))
join-commFun-sphere→Join zero zero (push a b i) j = lem j i
  where
  main : (a b : Bool) → sym (σS (b ⌣S a)) ≡ cong (-S^ 1) (σS (a ⌣S b))
  main false false = refl
  main false true = refl
  main true false = refl
  main true true = refl

  lem : Square (sym (σS (b ⌣S a))) (cong (-S^ 1) (σS (a ⌣S b)))
               (refl ∙ (refl ∙ refl)) (refl ∙ (refl ∙ refl))
  lem = flipSquare (sym (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl))
    ◁ flipSquare (main a b)
    ▷ (rUnit refl ∙ cong₂ _∙_ refl (rUnit refl)))

join-commFun-sphere→Join zero (suc m) (push a b i) j =
  comp (λ k → S₊ (suc (+-comm zero (suc m) (j ∧ k))))
       (λ k →
      λ{(i = i0) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
                   ▷ sym (-S^pt (suc (·-comm zero m k)))) j
      ; (i = i1) → ((λ i → ptSn (suc (+-comm zero (suc m) (i ∧ k))))
                   ▷ sym (-S^pt (suc (·-comm zero m k)))) j
      ; (j = i0) → σSn (suc m) (b ⌣S a) (~ i)
      ; (j = i1) → -S^ (suc (·-comm zero m k))
                      (σS (toPathP {A = λ i → S₊ (+-comm zero (suc m) i)}
                                   (sym (comm⌣S a b)) k) i)})
   (hcomp (λ k →
      λ{(i = i0) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
      ; (i = i1) → lUnit (λ r → -S^pt (suc zero) (~ r ∨ ~ k)) k j
      ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
      ; (j = i1) → cong-S^σ m (suc zero) (b ⌣S a) k i})
       (σ (S₊∙ (suc m)) (-S^ 1 (b ⌣S a)) i))
  where
  n = zero
  lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
  lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
      ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
      ∙ -S^·2 (m · n) (b ⌣S a)

join-commFun-sphere→Join (suc n') m (push a b i) j =
  comp (λ k → S₊ (suc (+-comm n m (j ∧ k))))
       (λ k →
      λ{(i = i0) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
                  ▷ sym (-S^pt (suc (m · n)))) j
      ; (i = i1) → ((λ i → ptSn (suc (+-comm n m (i ∧ k))))
                  ▷ sym (-S^pt (suc (m · n)))) j
      ; (j = i0) → σSn (n + m) (b ⌣S a) (~ i)
      ; (j = i1) → -S^ (suc (m · n))
                        (σS (toPathP {A = λ i → S₊ (+-comm n m i)}
                                 (sym (comm⌣S a b)) k) i)})
   (hcomp (λ k →
      λ{(i = i0) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
      ; (i = i1) → lUnit (λ r → -S^pt (suc (m · n)) (~ r ∨ ~ k)) k j
      ; (j = i0) → σS-S^ 1 (b ⌣S a) k i
      ; (j = i1) → cong-S^σ (n' + m) (suc (m · n))
                             (-S^ (n · m) (b ⌣S a)) k i})
      (σ (S₊∙ (suc (n' + m))) (invSphere (lem (~ j))) i))
  where
  n = suc n'
  lem : -S^ (m · n) (-S^ (n · m) (b ⌣S a)) ≡ b ⌣S a
  lem = cong (-S^ (m · n)) (cong₂ -S^ (·-comm n m) refl)
      ∙ -S^-comp (m · n) (m · n) (b ⌣S a)
      ∙ -S^·2 (m · n) (b ⌣S a)

-- todo: move elsewhere
open import Cubical.Data.Empty as ⊥

private
  -S^σS-lem : (n m : ℕ) (a : S₊ n) (b : S₊ m)
    → (1 ≤ n + m)
    → PathP
      (λ i₁ → -S^∙ {k = +-comm m n (~ i₁)} (suc (m · n)) .snd i₁
             ≡ -S^∙ (suc (m · n)) .snd i₁)
      ((cong (-S^ (suc (m · n)))
             (σS (subst S₊ (+-comm m n) (-S^ (m · n) (b ⌣S a))))))
      (σS (-S^ (suc (m · n)) (-S^ (m · n) (b ⌣S a))))
  -S^σS-lem zero zero a b ineq = ⊥.rec (snotz (+-comm 1 (ineq .fst) ∙ snd ineq))
  -S^σS-lem zero (suc m) a b ineq i j =
    cong-S^σ _ (suc (m · zero))
     (transp (λ j → S₊ (+-comm (suc m) zero (j ∧ ~ i)))
             i (-S^ (suc m · zero) (b ⌣S a))) (~ i) j
  -S^σS-lem (suc n) zero a b ineq i j =
    cong-S^σ _ (suc zero)
     (transp (λ j → S₊ (+-comm zero (suc n) (j ∧ ~ i)))
             i (b ⌣S a)) (~ i) j
  -S^σS-lem (suc n) (suc m) a b ineq i j =
    cong-S^σ _ (suc (suc m · suc n))
                   (transp (λ j → S₊ (+-comm (suc m) (suc n) (j ∧ ~ i)))
                           i (-S^ (suc m · suc n) (b ⌣S a))) (~ i) j

open import Cubical.HITs.Truncation as TR
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation as PT


join→Sphere∘join-commFunId : (n m : ℕ) (x : _)
  → PathP (λ i → S₊ (suc (+-comm m n (~ i))))
           (-S^ (suc (m · n)) (join→Sphere n m x))
           (join→Sphere m n (join-commFun x))
join→Sphere∘join-commFunId n m (inl x) i = -S^∙ (suc (m · n)) .snd i
join→Sphere∘join-commFunId n m (inr x) i = -S^∙ (suc (m · n)) .snd i
join→Sphere∘join-commFunId zero zero (push a b i) j =
  (sym (rUnit refl) ◁  flipSquare (lem a b) ▷ rUnit refl) i j
  where
  lem : (a b : Bool) → cong invSphere (σS (a ⌣S b)) ≡ sym (σS (b ⌣S a))
  lem false false = refl
  lem false true = refl
  lem true false = refl
  lem true true = refl
join→Sphere∘join-commFunId (suc n') zero (push a b i) j = lem j i
  where
  n = suc n'
  m = zero
  lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
                (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
                (sym (σS (b ⌣S a)))
                (λ i → -S^∙ (suc (m · n)) .snd i)
                λ i → -S^∙ (suc (m · n)) .snd i
  lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
             (comm⌣S a b)
      ◁ -S^σS-lem n zero a b (n' + zero , +-comm (n' + zero) 1)
      ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
               ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
                               ∙ -S^·2 (m · n) (b ⌣S a)))
           ∙ σ-invSphere _ (b ⌣S a))
join→Sphere∘join-commFunId n (suc m') (push a b i) j = lem j i
  where
  m = suc m'
  lem : SquareP (λ i j → S₊ (suc (+-comm m n (~ i))))
                (cong (-S^ (suc (m · n))) (σS (a ⌣S b)))
                (sym (σS (b ⌣S a)))
                (λ i → -S^∙ (suc (m · n)) .snd i)
                λ i → -S^∙ (suc (m · n)) .snd i
  lem = cong (congS (-S^ (suc (m · n))) ∘ σS)
             (comm⌣S a b)
      ◁ -S^σS-lem n (suc m') a b (n + m' , +-comm (n + m') 1 ∙ sym (+-suc n m'))
      ▷ (cong σS ((λ i → -S^ (suc (m · n)) (-S^ ((m · n)) (b ⌣S a)))
               ∙ cong invSphere (-S^-comp (m · n) (m · n) (b ⌣S a)
                               ∙ -S^·2 (m · n) (b ⌣S a)))
           ∙ σ-invSphere _ (b ⌣S a))

[_∣_]π'-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
    → [ f ∣ g ]π'
      ≡ subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
              (-π^ (suc (suc m · suc n)) [ g ∣ f ]π')
[_∣_]π'-comm {X = X} {n} {m} =
  PT.rec (isPropΠ2 (λ _ _ → squash₂ _ _)) (λ main →
  ST.elim2 (λ _ _ → isSetPathImplicit)
  λ f g → cong ∣_∣₂
    (cong (λ f → _∘∙_ {A = S₊∙ (suc (suc (n + suc m)))}
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

[_∣_]π'-jacobi* : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X) (h : π' (suc (suc l)) X)
  → [ f ∣ [ g ∣ h ]π' ]π*
   ≡ ·π* {![ [ f ∣ g ]π' ∣ h ]π*!} {!!}
[_∣_]π'-jacobi* {X = X} {n} {m} {l} = {!!}
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.SmashProduct

joinPinchComp : ∀ {ℓ ℓ' ℓ'' ℓA ℓB} {X : Pointed ℓ}
  {A : Type ℓA} {B : Type ℓB}
  {A' : Type ℓ'} {B' : Type ℓ''}
  (g : A → A') (h : B → B') 
  → (f : A' → B' → Ω X .fst) (x : join A B)
  → joinPinch X f (join→ g h x)
   ≡ joinPinch X (λ a b → f (g a) (h b)) x
joinPinchComp {X = X} g h f (inl x) = refl
joinPinchComp {X = X} g h f (inr x) = refl
joinPinchComp {X = X} g h f (push a b i) = refl

open import Cubical.Foundations.Pointed.Homogeneous

Ω→σ : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
  (f : Susp∙ (typ A) →∙ B)
  (g : C →∙ A)
  → (Ω→ f  ∘∙ (((σ A) , (rCancel _)) ∘∙ g))
   ≡ (Ω→ (f ∘∙ suspFun∙ (fst g)) ∘∙ (σ C , rCancel _))
Ω→σ {A = A} {B} {C} f g =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt (λ x →
        cong (Ω→ f .fst)
          (sym (cong-∙ (suspFun (fst g)) (merid x) (sym (merid (pt C)))
                      ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (snd g))))))
  ∙ cong₂ _∘∙_ (cong Ω→ (ΣPathP (refl , lUnit (snd f)))) refl

private
  assocPath : (n m l : ℕ) → _ ≡ _
  assocPath n m l = (+-assoc (suc m) (suc n) (suc l)
                          ∙ cong (_+ suc l) (+-comm (suc m) (suc n))
                          ∙ +-assoc (suc n) (suc m) (suc l) ⁻¹)

SphereSmashIso∙ : (n m : ℕ) → Iso.fun (SphereSmashIso n m) (inl tt) ≡ ptSn (n + m)
SphereSmashIso∙ zero m = refl
SphereSmashIso∙ (suc n) m = refl

suspFun∙Cancel : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : Iso A B)
  → suspFun∙ (fun f) ∘∙ suspFun∙ (inv f)  ≡ id∙ (Susp∙ B)
suspFun∙Cancel f = ΣPathP ((funExt (rightInv (congSuspIso f)))
  , sym (rUnit refl))

SphereSmashIso⁻∙ : (n m : ℕ) → Iso.inv (SphereSmashIso n m) (ptSn (n + m)) ≡ inl tt
SphereSmashIso⁻∙ n m =
    sym (cong (Iso.inv (SphereSmashIso n m)) (SphereSmashIso∙ n m))
  ∙ Iso.leftInv (SphereSmashIso n m) (inl tt)

open import Cubical.HITs.Join.CoHSpace
kabul = ·Π≡+*
[_∣_]π'-jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X) (h : π' (suc (suc l)) X)
  → [ f ∣ [ g ∣ h ]π' ]π'
   ≡ ·π' _ (subst (λ k → π' k X)
                  (cong (2 +_) (sym (+-assoc n (suc m) (suc l))))
                  ([ [ f ∣ g ]π' ∣ h ]π'))
           (subst (λ k → π' k X)
                  (cong suc (assocPath n m l))
                  [ g ∣ [ f ∣ h ]π' ]π')
[_∣_]π'-jacobi {X = X} {n} {m} {l} =
  ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂
      ((cong₂ _∘∙_ (ΣPathP ((cong (joinPinch X) refl
     ∙ cong (joinPinch X)
        (funExt (λ a → funExt λ b →
          cong₂ _∙_ (
            ((λ i → Ω→ (lem1 g h i) .fst (σS b) )
           ∙ (sym (funExt⁻ (cong fst (Ω→σ (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h ∘∙
                   SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l)))
                   (inv (SphereSmashIso (suc m) (suc l))
                 , λ k → SphereSmashIso⁻∙ (suc m) (suc l) k))) b)
                       ))) refl))
     ∙ funExt λ r → sym (joinPinchComp {X = X}
           (idfun (S₊ (suc n)))
           (inv (SphereSmashIso (suc m) (suc l)))
           (λ a b →
             Ω→ (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h
                ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))) .fst
             (σ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) b)
            ∙ Ω→ f .fst (σ (S₊∙ (suc n)) a)) r))
            , {!!}))
       refl
      ∙ ∘∙-assoc _ _ _)
      ∙ (λ i → asd f g h i
             ∘∙ ((join→ (idfun _) (inv (SphereSmashIso (suc m) (suc l))) , refl)
             ∘∙ (sphere→Join (suc n) (suc m + suc l) , refl))))
             ∙ refl
             ∙ {!cong ∣_∣₂ (sym (·Π≡+* _ _))!}
             ∙ {!+*≡·Π!}

  where
  lem3 : (join→Sphere (suc m) (suc l) , refl)
         ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))
       ≡ suspFun∙ (fun (SphereSmashIso (suc m) (suc l)))
  lem3 = ΣPathP ((funExt (
    λ { north → refl
      ; south → merid (ptSn (suc m + suc l))
      ; (merid a i) j → lem4 a j i}))
      , sym (rUnit _)
      ∙ cong sym (cong σS (IdR⌣S {n = suc m} {suc l} (ptSn (suc l))) ∙ σS∙))
    where
    lem4 : (t : _)
      → Square (cong (join→Sphere (suc m) (suc l) ∘ SuspSmash→Join) (merid t))
                (merid (fun (SphereSmashIso (suc m) (suc l)) t))
                refl
                (merid (ptSn (suc (m + suc l))))
    lem4 = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
      λ x y → (cong-∙∙ (join→Sphere (suc m) (suc l)) (sym (push x (ptSn (suc l)))) (push x y) (sym (push (ptSn (suc m)) y))
        ∙ cong₃ _∙∙_∙∙_
                (cong sym (cong σS (IdL⌣S {n = suc m} {suc l} x)
                          ∙ σS∙))
                refl
                (cong sym (cong σS (IdR⌣S {n = suc m} {suc l} y)
                          ∙ σS∙))
        ∙ sym (rUnit (σS (x ⌣S y))))
        ◁ symP (compPath-filler (merid (x ⌣S y))
                                (sym (merid (ptSn (suc m + suc l)))))

  lem2 : SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))
       ∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l)))
       ≡ (sphere→Join (suc m) (suc l) , refl)
  lem2 = sym (cong ((sphere→Join (suc m) (suc l) , refl) ∘∙_)
                   (∘∙-assoc _ _ _) -- 
             ∙ sym (∘∙-assoc _ _ _)
             ∙ cong₂ _∘∙_
             (ΣPathP ((funExt (leftInv (IsoSphereJoin (suc m) (suc l))))
                    , (sym (rUnit refl)
    ◁ flipSquare (cong₂ _∙_ refl
        (cong₂ _∙_ (cong-∙∙  (fun SmashJoinIso) refl refl refl
          ∙ sym (rUnit refl)) refl
          ∙ sym (lUnit _))
        ∙ rCancel _)))) refl
             ∙ ∘∙-idʳ _)
       ∙ cong ((sphere→Join (suc m) (suc l) , refl) ∘∙_)
                (cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l))))
                  lem3)
       ∙ cong₂ _∘∙_ refl (suspFun∙Cancel (SphereSmashIso (suc m) (suc l)))
       ∙ ∘∙-idˡ _

  module _ (g : S₊∙ (suc (suc m)) →∙ X)
           (h : S₊∙ (suc (suc l)) →∙ X) where
    lem1 : [ g ∣ h ] ≡ ((·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h
      ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l)))
        ∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l))))
    lem1 = cong₂ _∘∙_ refl refl
         ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h ∘∙_)
                (sym lem2)
         ∙ sym (∘∙-assoc _ _ _)

  rrrr = SuspSmash→Join∙
  module _ (f : S₊∙ (suc (suc n)) →∙ X) (g : S₊∙ (suc (suc m)) →∙ X)
           (h : S₊∙ (suc (suc l)) →∙ X) where
    asd : {!!}
    asd = JacobiR' (S₊∙ (suc n)) (S₊∙ n)
                   (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
                   (S₊∙ (suc m)) (S₊∙ m)
                   (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
                   (S₊∙ (suc l)) (S₊∙ l)
                   (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
                   f g h
