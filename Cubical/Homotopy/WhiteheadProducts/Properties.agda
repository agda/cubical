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
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Properties

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

open import Cubical.Homotopy.WhiteheadProducts.Generalised.Properties
open import Cubical.Homotopy.Group.Join
open import Cubical.HITs.SetTruncation

-π^ : ∀ {ℓ} {k : ℕ} {A : Pointed ℓ} (n : ℕ) → π' (suc k) A → π' (suc k) A
-π^ {k = k} n = iter n (-π' k)

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

[_∣_]π'-comm : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       (f : π' (suc (suc n)) X) (g : π' (suc (suc m)) X)
    → [ f ∣ g ]π'
      ≡ subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
              (-π^ (n · m) [ g ∣ f ]π')
[_∣_]π'-comm {X = X} {n} {m} f g = {!!}
  where
  open import Cubical.HITs.SetTruncation as ST
  open import Cubical.Foundations.Transport
  open import Cubical.HITs.S1 hiding (_·_)
  
  com-main : (n m : ℕ) (t : π' (suc (n + m)) X)
    → (fun (π*SwapIso n m X) (inv (Iso-π*-π' n m) t))
      ≡ -π*^ (n · m) (inv (Iso-π*-π' m n)
           (subst (λ k → π' (suc k) X) (+-comm n m) t))
  com-main n m = ST.elim {!!}
    λ t → cong ∣_∣₂ (ΣPathP ({!!} , {!!}) ∙ {!!})
         ∙ sym (-π*^≡ (n · m) _)
    where
    invSphere∙ : (n : ℕ) → invSphere (ptSn (suc n)) ≡ ptSn (suc n)
    invSphere∙ zero = refl
    invSphere∙ (suc n) = merid (ptSn (suc n)) ⁻¹

    -- iter-const : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (a : A) → iter n (λ _ → 
    -- iter-const = ?

    -S^∙ : {k : ℕ} (n : ℕ) → -S^ {k = (suc k)} n (ptSn (suc k)) ≡ ptSn (suc k)
    -S^∙ zero = refl
    -S^∙ (suc n) = cong invSphere (-S^∙ n) ∙ invSphere∙ _

    open import Cubical.Data.Bool
    cong-S^ : {k : ℕ} (n : ℕ) (x : S₊ k)
      → PathP (λ i → -S^∙ {k = k} n i ≡ -S^∙ n i) (cong (-S^ n) (σS x)) (sym^ n (σS x))
    cong-S^ {k} zero x = refl
    cong-S^ {zero} (suc n) false = {!iterswap n invLooper!} ◁ {!!} ▷ {!!}
    cong-S^ {zero} (suc n) true =
      (λ i _ → -S^∙ {k = zero} (suc n) i) ▷ sym (sym^-refl (suc n))

    cong-S^ {suc k} (suc n) x i j = 
      hcomp (λ k → λ {(i = i0) → invSphere (iter n invSphere (σS x j))
                     ; (i = i1) → help k j})
            (invSphere (cong-S^ n x i j))
      where
      help : Square (cong invSusp (sym^ n (σS x))) (sym^ (suc n) (σS x))
                    (merid (ptSn _) ⁻¹) (merid (ptSn _) ⁻¹)
      help = (sym (cong (cong invSusp) (σS-S^ n x))
             ∙ cong-∙ invSusp (merid (-S^ n x)) (merid (ptSn (suc k)) ⁻¹))
            ◁ (λ i → compPath-filler (compPath-filler' (merid (ptSn _))
                        (sym (merid (-S^ n x))) i) (merid (ptSn _)) (~ i))
                   ▷ sym (symDistr _ _)
            ▷ (cong sym (σS-S^ n x))

{-
Goal: S₊ (suc k)
———— Boundary (wanted) —————————————————————————————————————
j = i0 ⊢ hcomp
         (doubleComp-faces (λ _ → invSphere (-S^ n (ptSn (suc k))))
          (invSphere∙ (suc k)) i)
         (invSphere (-S^∙ n i))
j = i1 ⊢ hcomp
         (doubleComp-faces (λ _ → invSphere (-S^ n (ptSn (suc k))))
          (invSphere∙ (suc k)) i)
         (invSphere (-S^∙ n i))
i = i0 ⊢ invSphere (iter n invSphere (σS x j))
i = i1 ⊢ iter n (λ p i₁ → p (~ i₁)) (σS x) (~ j)
-}


    open import Cubical.Homotopy.Loopspace
    p : (j : I) → _
    p j = doubleWhiskFiller refl (λ i → ptSn (suc (+-comm n m i))) (sym (-S^∙ (suc (n · m)))) j -- (λ i → ptSn (suc (+-comm n m i))) ▷ sym (-S^∙ (suc (n · m)))

    help : (x : _) → PathP (λ i → S₊ (suc (+-comm n m i)))
                            (join→Sphere n m (join-commFun x))
                            (-S^ (suc (n · m)) ((join→Sphere m n x)))
    help (inl x) = p i1
    help (inr x) = p i1
    help (push a b i) j = help' j i
      where
      help' : SquareP (λ i j → S₊ (suc (+-comm n m i)))
                (sym (σSn (n + m) (b ⌣S a)))
                (cong (-S^ (suc (n · m))) (σS (a ⌣S b)))
                (p i1) (p i1)
      help' = cong sym (cong (σSn (n + m)) (comm⌣S b a))
            ◁ (cong sym (sym (substCommSlice S₊
                              (λ x → Ω (S₊∙ (suc x)) .fst)
                              (λ _ → σS) (+-comm m n)
                              _))
             ◁ transport (λ j → PathP (λ i → p j i ≡ p j i)
                         (sym (subst (λ x → Ω (S₊∙ (suc x)) .fst)
                                  (isSetℕ _ _ (+-comm m n) (sym (+-comm n m)) (~ j))
                              (σSn (m + n) (-S^ (m · n) (a ⌣S b)))))
                         (doubleCompPath-filler (sym (-S^∙ (suc (n · m))))
                                                (cong (-S^ (suc (n · m))) (σS (a ⌣S b)))
                                                ((-S^∙ (suc (n · m)))) (~ j)))
               (toPathP (transport⁻Transport (λ i₁ → p i0 (~ i₁) ≡ p i0 (~ i₁)) _
                      ∙ transport (PathP≡doubleCompPathʳ _ _ _ _) {!!})))
  com : (n m : ℕ) (t : π' (suc (n + m)) X)
    →  (fun (π*SwapIso n m X) (inv (Iso-π*-π' n m) t))
     ≡ inv (Iso-π*-π' m n) (subst (λ k → π' (suc k) X) (+-comm n m)
        (-π^ (n · m) t))
  com n m = ST.elim {!!}
    λ t → cong ∣_∣₂ (ΣPathP ((funExt (λ x → cong (fst t) {!!})) , {!!})) ∙ {!!}

  main : Iso.inv (π*Gr≅π'Gr (suc n) (suc m) X .fst) ([ f ∣ g ]π')
       ≡ Iso.inv (π*Gr≅π'Gr (suc n) (suc m) X .fst)
                 (subst (λ k → π' (suc k) X) (+-comm (suc m) (suc n))
                   (-π^ (n · m) [ g ∣ f ]π' ))
  main = whπ'≡whπ* f g
       ∙ [ f ∣ g ]π*-comm
       ∙ {!!}
  
