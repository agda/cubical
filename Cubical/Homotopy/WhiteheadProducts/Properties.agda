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
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base
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

open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Properties
-- JacobiΣR
open import Cubical.HITs.Join.CoHSpace
open import Cubical.Homotopy.HSpace
open HSpace
module _ {ℓ} (jS : ℕ → ℕ → Pointed₀)
    (jS≃S : (n m : ℕ) → jS n m ≃∙ S₊∙ (suc (n + m)))
    (Sm : ℕ → ℕ → Pointed₀)
    (Sm≃S : (n m : ℕ) → Sm n m ≃∙ S₊∙ (n + m))
    (brack1 : (n m : ℕ) (X : Pointed ℓ)
              (f : S₊∙ (suc n) →∙ X)
              (g : S₊∙ (suc m) →∙ X)
           → jS n m →∙ X)
    (brack2 : (n m : ℕ) (X : Pointed ℓ)
              (f : S₊∙ (suc n) →∙ X)
              (g : S₊∙ (suc m) →∙ X)
           → (S₊∙ (suc (n + m)) →∙ X))
    (brack≡ : (n m : ℕ) (X : Pointed ℓ)
      (f : S₊∙ (suc n) →∙ X) (g : S₊∙ (suc m) →∙ X)
      → brack1 n m X f g
        ∘∙ ≃∙map (invEquiv∙ (jS≃S n m))
       ≡ brack2 n m X f g)
    (comm-jS∙ : (n m : ℕ) → jS n m ≃∙ jS m n)
    (comm-jSinv : (n m : ℕ) (X : Pointed ℓ)
      → PathP (λ i → jS n m →∙ S₊∙ (suc (+-comm n m i)))
          (-S^∙ (suc (n · m)) ∘∙ ≃∙map (jS≃S n m))
          (≃∙map (jS≃S m n) ∘∙ ≃∙map (comm-jS∙ n m)))
    (hSpace-jS : (X : Pointed ℓ) {n m : ℕ}
           → HSpace (jS n m →∙ X ∙))
    (assoc-jS : (X : Pointed ℓ) {n m : ℕ}
          → AssocHSpace (hSpace-jS X {n = n} {m}))
    (hSpacePres : (X : Pointed ℓ) {n m : ℕ}
      → (f g : S₊∙ (suc (n + m)) →∙ X)
      → (∙Π f g ∘∙ ≃∙map (jS≃S n m))
       ≡ μ (hSpace-jS X) (f ∘∙ ≃∙map (jS≃S n m))
                         (g ∘∙ ≃∙map (jS≃S n m)))
    (jac : (n m l : ℕ) (X : Pointed ℓ)
           (f : S₊∙ (suc (suc n)) →∙ X)
           (g : S₊∙ (suc (suc m)) →∙ X)
           (h : S₊∙ (suc (suc l)) →∙ X)
        → brack1 (suc n) (suc (m + suc l)) X
                 f (brack1 (suc m) (suc l) X g h
                 ∘∙ (≃∙map (invEquiv∙ (jS≃S (suc m) (suc l)))))
         ≡ μ (hSpace-jS X)
             {!brack1!}
             {!!})
         {-
             (brack1 _ _ X (brack1 (suc n) (suc m) X f g
             ∘∙ (≃∙map (invEquiv∙ (jS≃S (suc n) (suc m))))) h
             ∘∙ {!Sm≃S n m!})
             (brack1 _ _ X g
               (brack1 _ _ X f h ∘∙ {!brack1 n m X ? ?!})
             ∘∙ {!!}))
             -}
    (jac' : (n m l : ℕ) (X : Pointed ℓ)
           (f : S₊∙ (suc (suc n)) →∙ X)
           (g : S₊∙ (suc (suc m)) →∙ X)
           (h : S₊∙ (suc (suc l)) →∙ X)
        → brack1 (suc n) (suc (m + suc l)) X
                 f (brack1 (suc m) (suc l) X g h
                 ∘∙ (≃∙map (invEquiv∙ (jS≃S (suc m) (suc l)))))
         ≡ μ (hSpace-jS X)
             (brack1 _ _ X (brack1 (suc n) (suc m) X f g
             ∘∙ (≃∙map (invEquiv∙ (jS≃S (suc n) (suc m))))) h
             ∘∙ {!Sm≃S n m!})
             {!map≃comm-jS∙ (suc n) (suc m + suc l))!})
  where
  JacobiType : Type _
  JacobiType = (n m : ℕ) (X : Pointed ℓ)
    → {!!} ≡ {!!}

lem : ∀ {ℓ} (jS : ℕ → ℕ → Pointed ℓ-zero)
    (jS≃S : (n m : ℕ) → jS n m ≃∙ S₊∙ (suc (n + m)))
    (hSpace-jS : (X : Pointed ℓ) {n m : ℕ}
           → HSpace (jS n m →∙ X ∙))
    (assoc-jS : (X : Pointed ℓ) {n m : ℕ}
          → AssocHSpace (hSpace-jS X {n = n} {m}))
    (hSpacePres : (X : Pointed ℓ) {n m : ℕ}
      → (f g : S₊∙ (suc (n + m)) →∙ X)
      → (∙Π f g ∘∙ ≃∙map (jS≃S n m))
       ≡ μ (hSpace-jS X) (f ∘∙ ≃∙map (jS≃S n m))
                         (g ∘∙ ≃∙map (jS≃S n m)))
    → {!!}
    → {!!} -- 
    → {!coHSpace!}
lem = {!·whΣ≡·wh!}

fafaafaf = JacobiΣR

open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.SmashProduct.SymmetricMonoidal

kabul = ·Π≡+*

wh∘∙eq' : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  → {B' : Pointed ℓ'} → (e : B' ≃∙ B)
  → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B') →∙ C)
  → (·whΣ A B' f g)
   ≡ (·whΣ A B f (g ∘∙ suspFun∙ (invEq (fst e)))
   ∘∙ suspFun∙ (idfun∙ A ⋀→ ≃∙map e))
wh∘∙eq' {A = A} {B} {C} {B'} = {!!}

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

wh∘∙eqL : ∀ {ℓ ℓ' ℓ''} {A A' : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} (e : A' ≃∙ A)
  → (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
  → ·whΣ A' B (f ∘∙ suspFun∙ (fst (fst e))) g
  ≡ (·whΣ A B f g ∘∙ suspFun∙ (≃∙map e ⋀→ idfun∙ B))
wh∘∙eqL {A = A} {B} {C} {B'} = {!!}


open import Cubical.Foundations.Equiv.HalfAdjoint

retEqIsoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (is : Iso A B) (x : _)
    → retEq (isoToEquiv is) x
     ≡ ((sym (leftInv is (inv is (fun is x)))
     ∙ cong (inv is) ((rightInv is (fun is x)))))
     ∙ leftInv is x
retEqIsoToEquiv is x i j =
  hcomp (λ k → λ {(i = i1) → compPath-filler (sym (leftInv is (inv is (fun is x)))
                              ∙ cong (inv is) ((rightInv is (fun is x)))) (leftInv is x) k j
                  ; (j = i0) → (cong (inv is) (sym (rightInv is (fun is x)))
                              ∙ leftInv is (inv is (fun is x))) (i ∨ k)
                  ; (j = i1) → lUnit (leftInv is x) (~ i) k
                  })
    (lemma j i)
  where
  p = sym (symDistr (sym (leftInv is (inv is (fun is x))))
                        (cong (inv is) (rightInv is (fun is x))))
  lemma : Square (cong (inv is) (sym (rightInv is (fun is x)))
                ∙ leftInv is (inv is (fun is x)))
          refl refl
          (sym (leftInv is (inv is (fun is x)))
         ∙ cong (inv is) ((rightInv is (fun is x))))
  lemma = p ◁ λ i j → p i1 (~ i ∧ j)

[]≡·whΣ : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
  (f : S₊∙ (2 + n) →∙ X) (g : S₊∙ (2 + m) →∙ X)
  →  [ f ∣ g ]
   ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g
   ∘∙ suspFun∙ (inv (SphereSmashIso (suc n) (suc m))))
[]≡·whΣ {X = X} {n} {m} f g =
    cong₂ _∘∙_ (·whΣ≡·wh _ _ _ _) refl
  ∙ ∘∙-assoc _ _ _
  ∙ cong₂ _∘∙_ refl
    (Iso.inv (congIso (invIso (post∘∙equiv (joinSphereEquiv∙ (suc n) (suc m)))))
      (-- ∘∙-assoc _ _ _
       (cong₂ _∘∙_ (cong₂ _∘∙_ refl (ΣPathP
         (refl , (sym (lem') ∙ lUnit _)))) refl
       ∙ Iso.leftInv (post∘∙equiv (joinSphereEquiv∙ (suc n) (suc m)))
          (Join→SuspSmash∙ (S₊∙ (suc n)) (S₊∙ (suc m))))
     ∙ ΣPathP ((funExt (λ { (inl x) → refl
                          ; (inr x) → sym (merid (inl tt))
                          ; (push a b i) j → main a b (~ j) i}))
                          , rUnit refl)))
  where
  main : (a : S₊ (suc n)) (b : S₊ (suc m))
    → Square (cong (suspFun (inv (SphereSmashIso (suc n) (suc m))))
                   (σ (S₊∙ (suc n + suc m)) (a ⌣S b)))
              (merid (inr (a , b)))
              refl
              (merid (inl tt))
  main a b = (cong-∙ (suspFun (inv (SphereSmashIso (suc n) (suc m)))) _ _
    ∙ cong₂ _∙_ (cong merid (leftInv (SphereSmashIso (suc n) (suc m))
                                     (inr (a , b))))
                (cong (sym ∘ merid) (SphereSmashIso⁻∙ (suc n) (suc m))))
    ◁ symP (compPath-filler (merid (inr (a , b))) (sym (merid (inl tt))))

  retEqInvEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) (x : _) → retEq e x ≡ secEq (invEquiv e) x 
  retEqInvEquiv e x = refl

  p1 : leftInv (joinSphereIso' (suc n) (suc m)) (inl (ptSn (suc n))) ≡ sym (push (ptSn (suc n)) (ptSn (suc m)))
  p1 = cong₂ _∙_ (cong (congS (inv (invIso SmashJoinIso))) (sym (rUnit refl))) refl
     ∙ sym (lUnit _)

  p2 : rightInv (joinSphereIso' (suc n) (suc m)) north ≡ sym (merid (ptSn (suc n + suc m)))
  p2 = cong₂ _∙_ (cong (sym ∘ merid) (IdL⌣S {n = suc n} {m = suc m} (ptSn (suc n))))
       (sym (rUnit refl))
       ∙ sym (rUnit _)

  compPath-filler-diag : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → Path (Path A _ _) (λ i → compPath-filler p q (~ i) i) p
  compPath-filler-diag p q j i = compPath-filler p q (~ i ∧ ~ j) i

  lem' : retEq (isoToEquiv (IsoSphereJoin (suc n) (suc m))) (inl (ptSn (suc n))) ≡ refl
  lem' = retEqIsoToEquiv (IsoSphereJoin (suc n) (suc m)) (inl (ptSn (suc n)))
       ∙ cong₂ _∙_ (cong₂ _∙_ (cong sym (cong₂ _∙_ refl p1 ∙ rCancel _)
               ∙ refl) (cong-∙ (sphere→Join (suc n) (suc m)) _ _
                     ∙ cong₂ _∙_ refl (cong (congS (sphere→Join (suc n) (suc m))) p2
                       ∙ refl) -- cong sym (cong₂ _∙_ refl refl) ∙ {!!})
                     ∙ refl) ∙ sym (lUnit _)) (cong₂ _∙_ refl p1
                     ∙ rCancel _)
       ∙ sym (rUnit _)
       ∙ cong₂ _∙_
         (λ j i → sphere→Join (suc n) (suc m)
               (compPath-filler
                 (merid (sphereFun↑ _⌣S_ (ptSn (suc n)) (pt (S₊∙ (suc m)))))
                 (sym (merid (ptSn (suc (n + suc m))))) (~ i ∧ ~ j) i))
         refl
       ∙ cong₂ _∙_ (cong₂ _∙_ refl (cong (congS (inv (joinSphereIso' (suc n) (suc m))) ∘ merid) (IdL⌣S {n = suc n} {m = suc m} (ptSn (suc n))))) refl
       ∙ rCancel _

tripleSmasherL≃∙ : {n m l : ℕ}
  → S₊∙ (suc n + (suc m + suc l))
  ≃∙ S₊∙ (suc n) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))
tripleSmasherL≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m + suc l)))
                        , SphereSmashIso⁻∙ (suc n) (suc m + suc l))
             (⋀≃ (idEquiv∙ (S₊∙ (suc n)))
             ((isoToEquiv (invIso (SphereSmashIso (suc m) (suc l)))) , (SphereSmashIso⁻∙ (suc m) (suc l)))
            , refl)

tripleSmasherR≃∙ : {n m l : ℕ}
  → S₊∙ ((suc n + suc m) + suc l)
  ≃∙ ((S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) ⋀∙ S₊∙ (suc l))
tripleSmasherR≃∙ {n = n} {m} {l} =
  compEquiv∙ (isoToEquiv (invIso (SphereSmashIso (suc n + suc m) (suc l)))
                        , SphereSmashIso⁻∙ (suc n + suc m) (suc l))
             (⋀≃ ((isoToEquiv (invIso (SphereSmashIso (suc n) (suc m)))) , (SphereSmashIso⁻∙ (suc n) (suc m)))
                 (idEquiv∙ (S₊∙ (suc l)))
            , refl)


tripleSmasherL : {n m l : ℕ} → {!!}
tripleSmasherL = {!!}


suspFun∙Comp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (g : B → C) (f : A → B) → suspFun∙ (g ∘ f) ≡ (suspFun∙ g ∘∙ suspFun∙ f)
suspFun∙Comp f g = ΣPathP ((suspFunComp f g) , rUnit refl)

suspFun∙idfun : ∀ {ℓ} {A : Type ℓ}
  → suspFun∙ (idfun A) ≡ idfun∙ _
suspFun∙idfun = ΣPathP (suspFunIdFun , refl)


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

·Susp≡ : ∀ {ℓ ℓ'} (A A' : Pointed ℓ) {X : Pointed ℓ'} (e : A ≃∙ A')
  → (f g : Susp∙ (typ A) →∙ X)
  → ·Susp A f g
   ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
               (g ∘∙ suspFun∙ (invEq (fst e)))
    ∘∙ suspFun∙ (fst (fst e)))
·Susp≡ A A' {X} = Equiv∙J (λ A e → (f g : Susp∙ (typ A) →∙ X) →
      ·Susp A f g
   ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
               (g ∘∙ suspFun∙ (invEq (fst e)))
     ∘∙ suspFun∙ (fst (fst e))))
 λ f g → sym (cong₂ _∘∙_ (cong₂ (·Susp A')
   (cong (f ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ f)
   (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g))
   (ΣPathP (suspFunIdFun , refl))
   ∙ ∘∙-idˡ (·Susp A' f g))


subst∙ : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
  → {x y : X} (p : x ≡ y) → A x →∙ A y 
subst∙ A p .fst = subst (fst ∘ A) p
subst∙ A p .snd i = transp (λ j → fst (A (p (i ∨ j)))) i (pt (A (p i)))

subst∙refl : ∀ {ℓ ℓA} {X : Type ℓ} (A : X → Pointed ℓA)
  → {x : X} → subst∙ A (refl {x = x}) ≡ idfun∙ (A x)
subst∙refl A {x} = ΣPathP ((funExt transportRefl)
  , (λ j i → transp (λ t → fst (A x)) (j ∨ i) (pt (A x))))

subst∙Id : ∀ {ℓ ℓA ℓB} {X : Type ℓ} (A : X → Pointed ℓA) {B : Pointed ℓB}
  → {x y : X} (p : x ≡ y) (f : A x →∙ B)
    → f ∘∙ subst∙ A (sym p) ≡ transport (λ i → A (p i) →∙ B) f 
subst∙Id A {B = B} {x = x} =
  J (λ y p → (f : A x →∙ B)
            → f ∘∙ subst∙ A (sym p)
            ≡ transport (λ i → A (p i) →∙ B) f)
    λ f → (cong₂ _∘∙_ refl (subst∙refl A) ∙ ∘∙-idˡ _)
         ∙ sym (transportRefl f) 

[_∣_]π'-jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
  (f : π' (suc (suc n)) X)
  (g : π' (suc (suc m)) X)
  (h : π' (suc (suc l)) X)
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
       (·whΣ-assocer f g h
      ∙ cong₂ _∘∙_
        (JacobiΣR' (S₊∙ (suc n)) (S₊∙ n)
          (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
          (S₊∙ (suc m)) (S₊∙ m)
          (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
          (S₊∙ (suc l)) (S₊∙ l)
          (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
          f g h) refl
      ∙ cong₂ _∘∙_ (·Susp≡ _ _ (invEquiv∙ tripleSmasherL≃∙) _ _) refl
      ∙ ∘∙-assoc _ _ _
      ∙ cong₂ _∘∙_ refl
        (sym (suspFun∙Comp _ _)
        ∙ cong suspFun∙ (funExt (retEq (fst tripleSmasherL≃∙))) ∙ suspFun∙idfun)
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
              (sym (sym (subst∙Id (S₊∙ ∘ suc)
                          (assocPath n m l)
                          [ g ∣ [ f ∣ h ] ])
                  ∙ {!!})))
  where
  s1 = subst∙ (S₊∙ ∘ (2 +_)) (+-assoc n (suc m) (suc l))
  s2 = subst∙ (S₊∙ ∘ suc) (sym (assocPath n m l))

  hoo : (a : S₊ (suc (n + (suc m + suc l))))
    → cong (suspFun (fst (fst tripleSmasherR≃∙)) ∘ fst s1)
           (merid a)
    ≡ merid (fun SmashAssocIso (invEq (fst (invEquiv∙ tripleSmasherL≃∙)) a))
  hoo a = (λ j i → suspFun (fst (fst tripleSmasherR≃∙))
                     (transp (λ i → S₊ (suc (suc (+-assoc n (suc m) (suc l) (i ∨ j))))) j
                     (merid (transp (λ i → S₊ (suc (+-assoc n (suc m) (suc l) (i ∧ j))))
                                    (~ j) a) i)))
        ∙ cong merid (inv (congIso (equivToIso (invEquiv (fst tripleSmasherR≃∙))))
                     (retEq (fst tripleSmasherR≃∙) _
                   ∙ fromPathP {!!}))


-- [_∣_]π'-jacobi : ∀ {ℓ} {X : Pointed ℓ} {n m l : ℕ}
--   (f : π' (suc (suc n)) X)
--   (g : π' (suc (suc m)) X)
--   (h : π' (suc (suc l)) X)
--   → [ f ∣ [ g ∣ h ]π' ]π'
--    ≡ ·π' _ (subst (λ k → π' k X)
--                   (cong (2 +_) (sym (+-assoc n (suc m) (suc l))))
--                   ([ [ f ∣ g ]π' ∣ h ]π'))
--            (subst (λ k → π' k X)
--                   (cong suc (assocPath n m l))
--                   [ g ∣ [ f ∣ h ]π' ]π')
-- [_∣_]π'-jacobi {X = X} {n} {m} {l} =
--   ST.elim3 (λ _ _ _ → isSetPathImplicit)
--     λ f g h → PT.rec (squash₂ _ _) (λ pathLem1 → cong ∣_∣₂
--        (cong₂ _∘∙_ (·whΣ≡·wh _ _ _ _
--                  ∙ refl)
--          refl
--       ∙ ∘∙-assoc _ _ _
--       ∙ cong₂ _∘∙_ (cong (wh-n-ml f)
--                    (cong₂ _∘∙_ (·whΣ≡·wh _ _ _ _)
--                    (λ _ → sphere→Join (suc m) (suc l)
--                         , (λ _ → inl (ptSn (suc m))))
--                    ∙ ∘∙-assoc _ _ _
--                    ∙ cong₂ _∘∙_ refl λ _ → cor (suc m) (suc l))) (λ _ → cor (suc n) (suc m + suc l))
--       ∙ lem1 f g h
--       ∙ cong₂ _∘∙_ (JacobiΣR' (S₊∙ (suc n)) (S₊∙ n)
--                               (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
--                               (S₊∙ (suc m)) (S₊∙ m)
--                               (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
--                               (S₊∙ (suc l)) (S₊∙ l)
--                               (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
--                               f g h)
--                    refl
--       ∙ cong₂ _∘∙_ (·Susp≡ _ _ e1 _ _) refl
--       ∙ ∘∙-assoc _ _ _
--       ∙ cong₂ _∘∙_ refl
--          (sym (∘∙-assoc _ _ _)
--         ∙ cong₂ _∘∙_ (sym (suspFun∙Comp _ _))
--                      (cor≡cor' n (m + suc l))
--         ∙ sym (suspFun∙Comp _ _)
--         ∙ cong suspFun∙
--           (cong (fun (SphereSmashIso (suc n) (suc m + suc l)) ∘_)
--             (cong (_∘ inv (SphereSmashIso (suc n) (suc (m + suc l))))
--               (sym (cong fst (⋀→∙-comp _ _ _ _))
--             ∙ cong₂ _⋀→_
--                 (cong₂ _∘∙_ refl (ΣPathP (refl , rUnit refl)))
--                 (cong₂ _∘∙_ refl (ΣPathP (refl , pathLem1 ∙ lUnit _)))
--             ∙ cong fst (⋀→∙-comp _ _ _ _)))
--           ∙ funExt (λ x →
--             cong (fun (SphereSmashIso (suc n) (suc m + suc l)))
--                  (secEq (⋀≃ {A = S₊∙ (suc n)}
--                             {S₊∙ (suc n)}
--                             {S₊∙ (suc m) ⋀∙ S₊∙ (suc l)}
--                             {S₊∙ (suc (m + suc l))} (idEquiv∙ _)
--                        (isoToEquiv (SphereSmashIso (suc m) (suc l)) , refl))
--                    ((inv (SphereSmashIso (suc n) (suc (m + suc l))) x)))
--           ∙ rightInv (SphereSmashIso (suc n) (suc (m + suc l))) x))
--         ∙ suspFun∙idfun)
--       ∙ ∘∙-idˡ _
--       ∙ cong₂ (·Susp (S₊∙ (suc (n + (suc m + suc l)))))
--               (∘∙-assoc _ _ _
--             ∙ sym (cong (subst (λ k → S₊∙ (2 + k) →∙ X)
--                         (sym (+-assoc n (suc m) (suc l))))
--                         (cong₂ _∘∙_
--                           (·whΣ≡·wh
--                             (S₊∙ (suc n + suc m))
--                             (S₊∙ (suc l))
--                             (·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g
--                             ∘∙ (sphere→Join (suc n) (suc m) , refl)) h
--                            ∙ cong₂ _∘∙_
--                              (cong (λ r → ·whΣ (S₊∙ (suc (n + suc m)))
--                                                 (S₊∙ (suc l)) r h)
--                                    (cong₂ _∘∙_
--                                      (·whΣ≡·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g)
--                                      refl
--                                    ∙ ∘∙-assoc _ _ _
--                                    ∙ λ i → ·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g ∘∙ cor≡cor' n m i)) refl
--                            ∙ cong₂ _∘∙_ (wh∘∙eqL (isoToEquiv (invIso (SphereSmashIso (suc n) (suc m))) , SphereSmashIso⁻∙ (suc n) (suc m))
--                            (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m)) f g) h) refl
--                            ∙ {!!})
--                           refl
--                         ∙ {!corEq⁻!} -- ∘∙-assoc _ _ _
--                         ∙ {!!} -- cong₂ _∘∙_ {!wh∘∙eqL -- (·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g)!} {!!}
--                         ∙ {![ g ∣ [ f ∣ h ] ]-pre!})
--               ∙ {!wh∘∙eqL -- ·whΣ≡·wh ? ? f ?!}))
--               {!-- transp (λ i → S₊∙ (suc (assocPath n m l i)) →∙ X) i0
-- [ g ∣ [ f ∣ h ] ]!}))
--       (pathLem m l)
--   where
--   pathLem : (m l : ℕ) → ∥ (SphereSmashIso⁻∙ (suc m) (suc l) ≡
--       retEq (isoToEquiv (SphereSmashIso (suc m) (suc l)))
--       (pt (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)))) ∥₁
--   pathLem m l = TR.rec (isProp→isOfHLevelSuc (m + l) squash₁)
--     ∣_∣₁
--    (isConnectedPath _
--     (isConnectedPath _
--      (subst2 isConnected (λ i → suc (suc (+-suc m l i)))
--       (isoToPath (invIso (SphereSmashIso (suc m) (suc l))))
--        (sphereConnected (suc m + suc l))) _ _) _ _ .fst)

--   suspFun∙Comp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
--     (g : B → C) (f : A → B) → suspFun∙ (g ∘ f) ≡ (suspFun∙ g ∘∙ suspFun∙ f)
--   suspFun∙Comp f g = ΣPathP ((suspFunComp f g) , rUnit refl)

--   suspFun∙idfun : ∀ {ℓ} {A : Type ℓ}
--     → suspFun∙ (idfun A) ≡ idfun∙ _
--   suspFun∙idfun = ΣPathP (suspFunIdFun , refl)

--   e1 : S₊∙ (suc n) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))
--     ≃∙ S₊∙ (suc n + (suc m + suc l))
--   e1 = compEquiv∙ (⋀≃ (idEquiv∙ _)
--                        (isoToEquiv (SphereSmashIso (suc m) (suc l)) , refl)
--                   , refl)
--                   (isoToEquiv (SphereSmashIso (suc n) (suc m + suc l)) , refl)
  
--   ·Susp≡ : ∀ {ℓ ℓ'} (A A' : Pointed ℓ) {X : Pointed ℓ'} (e : A ≃∙ A')
--     → (f g : Susp∙ (typ A) →∙ X)
--     → ·Susp A f g
--      ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
--                  (g ∘∙ suspFun∙ (invEq (fst e)))
--       ∘∙ suspFun∙ (fst (fst e)))
--   ·Susp≡ A A' {X} = Equiv∙J (λ A e → (f g : Susp∙ (typ A) →∙ X) →
--         ·Susp A f g
--      ≡ (·Susp A' (f ∘∙ suspFun∙ (invEq (fst e)))
--                  (g ∘∙ suspFun∙ (invEq (fst e)))
--        ∘∙ suspFun∙ (fst (fst e))))
--    λ f g → sym (cong₂ _∘∙_ (cong₂ (·Susp A')
--      (cong (f ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ f)
--      (cong (g ∘∙_) (ΣPathP (suspFunIdFun , refl)) ∙ ∘∙-idˡ g))
--      (ΣPathP (suspFunIdFun , refl))
--      ∙ ∘∙-idˡ (·Susp A' f g))

--   wh-n-ml = ·whΣ (S₊∙ (suc n)) (S₊∙ (suc (m + suc l))) {C = X}

--   sphere→Join≡∙ : (n m : ℕ) → sphere→Join n m (ptSn (suc (n + m))) ≡ inl (ptSn n)
--   sphere→Join≡∙ zero zero = sym (push true true)
--   sphere→Join≡∙ zero (suc m) = refl
--   sphere→Join≡∙ (suc n) m = refl

  
--   corEq⁻ : (n m : ℕ) → Susp∙ (S₊∙ n ⋀ S₊∙ m) ≃∙ S₊∙ (suc (n + m))
--   corEq⁻ n m = compEquiv∙ (isoToEquiv SmashJoinIso , refl)
--                (isoToEquiv (IsoSphereJoin n m) , refl)

--   cor'Eq⁻ : (n m : ℕ) → Susp∙ (S₊∙ (suc n) ⋀ S₊∙ m) ≃∙ S₊∙ (suc (suc n + m))
--   cor'Eq⁻ n m = isoToEquiv (congSuspIso (SphereSmashIso (suc n) m)) , refl

--   corEq⁻≡cor'Eq⁻ : (n m : ℕ) → corEq⁻ (suc n) m ≡ cor'Eq⁻ n m
--   corEq⁻≡cor'Eq⁻ n m = ΣPathP ((Σ≡Prop isPropIsEquiv
--       (funExt (λ { north → refl ; south → merid (ptSn (suc n + m))
--                  ; (merid a i) j → lemma a j i})))
--     , sym (rUnit refl))
--      where
--      lemma : (a : _) → Square (λ i → join→Sphere (suc n) m
--                                         (SuspSmash→Join (merid a i)))
--                                (merid (fst (⋀S∙ (suc n) m) a))
--                                refl (merid (ptSn (suc n + m)))
--      lemma = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
--        λ x y →
--        (cong-∙∙ (join→Sphere (suc n) m) _ _ _
--        ∙ cong₃ _∙∙_∙∙_ (cong sym (cong σS (IdL⌣S {n = suc n} {m = m} x) ∙ σS∙))
--                        (λ _ → σS (x ⌣S y))
--                        (cong sym (cong σS (IdR⌣S {n = suc n} {m = m} y) ∙ σS∙))
--        ∙ sym (rUnit _))
--        ◁ symP (compPath-filler (merid (x ⌣S y)) (sym (merid (ptSn (suc n + m)))))

--   cor : (n m : ℕ) → S₊∙ (suc (n + m)) →∙ Susp∙ (S₊∙ n ⋀ S₊∙ m)
--   cor n m = Join→SuspSmash∙ (S₊∙ n) (S₊∙ m)
--           ∘∙ (sphere→Join n m , sphere→Join≡∙ n m)

--   retEqComp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (a : A)
--     (e : A ≃ B) (g : B ≃ C)
--     → retEq (compEquiv e g) a
--      ≡ cong (invEq e) (retEq g (fst e a)) ∙ retEq e a 
--   retEqComp a e g = refl

--   cor≡corEq⁻ : (n m : ℕ) → ≃∙map (invEquiv∙ (corEq⁻ n m)) ≡ cor n m
--   cor≡corEq⁻ n m = ΣPathP (refl , {!!})
--   {-
--     ΣPathP (refl ,
--       (cong₂ _∙_
--         (cong (congS (Join→SuspSmash ∘ sphere→Join (suc n) m))
--                      (cong sym (sym (rUnit refl)))) refl
--     ∙ sym (lUnit _)
--     ∙ cong₂ _∙_  ((cong (congS (invEq (isoToEquiv SmashJoinIso)))
--                         (cong-∙∙ (inv (IsoSphereJoin (suc n) m))
--                            {!!}
--                            {!!}
--                            {!σS ?!}) ∙ {!!}) ∙ {!!}) {!cong!}
--     ∙ {!!}))
--     -}
--   {- ΣPathP (refl , (cong₂ _∙_ (cong (congS (Join→SuspSmash ∘ sphere→Join n m)) (cong sym (sym (rUnit refl)))) refl
--     ∙ sym (lUnit _)
--     ∙ cong₂ _∙_ {!!} {!cong!}
--     ∙ {!!}))
--     -}

--   asdda = SphereSmashIso∙

--   cor' : (n m : ℕ) → S₊∙ (suc ((suc n) + (suc m)))
--                    →∙ Susp∙ (S₊∙ (suc n) ⋀ S₊∙ (suc m))
--   cor' n m = suspFun∙ (inv (SphereSmashIso (suc n) (suc m)))


--   cor≡cor' : (n m : ℕ) → cor (suc n) (suc m) ≡ cor' n m
--   cor≡cor' n m = {!!}

--   lem1 : (f : S₊∙ (suc (suc n)) →∙ X) (g : _) (h : _)
--     → (wh-n-ml f
--        (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h
--         ∘∙ cor (suc m) (suc l))
--        ∘∙ cor (suc n) (suc (m + suc l)))
--        ≡ (·whΣ (S₊∙ (suc n)) (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) {C = X}
--                f (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h)
--        ∘∙ (suspFun∙ (idfun∙ _ ⋀→ (Iso.inv (SphereSmashIso (suc m) (suc l))
--                                 , SphereSmashIso⁻∙ (suc m) (suc l)))
--        ∘∙ cor (suc n) (suc (m + suc l))))
--   lem1 f g h =
--     cong₂  _∘∙_
--       (cong (wh-n-ml f)
--         (cong (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h ∘∙_)
--           (cor≡cor' m l)
--         ∙ refl)
--         ∙ wh∘∙eq ((invEquiv (isoToEquiv (SphereSmashIso (suc m) (suc l))))
--                 , (SphereSmashIso⁻∙ (suc m) (suc l)))
--                 f (·whΣ (S₊∙ (suc m)) (S₊∙ (suc l)) g h))
--       (λ _ → cor (suc n) (suc (m + suc l)))
--      ∙ ∘∙-assoc _ _ _


--   -- ST.elim3 (λ _ _ _ → isSetPathImplicit)
--   --   λ f g h →
--   --     cong ∣_∣₂
--   --     ((cong₂ _∘∙_ (ΣPathP ((cong (joinPinch X) refl
--   --    ∙ cong (joinPinch X)
--   --       (funExt (λ a → funExt λ b →
--   --         cong₂ _∙_ (
--   --           ((λ i → Ω→ (lem1 g h i) .fst (σS b) )
--   --          ∙ (sym (funExt⁻ (cong fst (Ω→σ (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h ∘∙
--   --                  SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l)))
--   --                  (inv (SphereSmashIso (suc m) (suc l))
--   --                , λ k → SphereSmashIso⁻∙ (suc m) (suc l) k))) b)
--   --                      ))) refl))
--   --    ∙ funExt λ r → sym (joinPinchComp {X = X}
--   --          (idfun (S₊ (suc n)))
--   --          (inv (SphereSmashIso (suc m) (suc l)))
--   --          (λ a b →
--   --            Ω→ (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h
--   --               ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))) .fst
--   --            (σ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)) b)
--   --           ∙ Ω→ f .fst (σ (S₊∙ (suc n)) a)) r))
--   --           , (flipSquare ((λ _ → refl ∙ refl ∙ refl)
--   --                        ∙ sym (lUnit (refl ∙ refl))
--   --                        ∙ sym (lUnit refl))
--   --           ▷ rUnit (refl {x = pt X}))))
--   --      refl
--   --     ∙ ∘∙-assoc _ _ _)
--   --     ∙ (λ i → asd f g h i
--   --            ∘∙ ((join→ (idfun _) (inv (SphereSmashIso (suc m) (suc l))) , refl)
--   --            ∘∙ (sphere→Join (suc n) (suc m + suc l) , refl))))
--   --            ∙ refl
--   --            ∙ cong ∣_∣₂ ((cong₂ _∘∙_ (cong₂ _+*_ (sym (rightInv fromSusp≅fromJoin _))
--   --                                                 (sym (rightInv fromSusp≅fromJoin _)))
--   --                                     refl)
--   --              ∙  cong (_∘∙ F1) (sym (fromSusp≅fromJoinPres+*
--   --                      (inv fromSusp≅fromJoin
--   --                           (·wh (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l))
--   --                             (·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g
--   --                             ∘∙  SuspSmash→Join∙ (S₊∙ (suc n)) (S₊∙ (suc m)))
--   --                           h
--   --                        ∘∙ Jcorrection₁ (S₊∙ (suc n)) (S₊∙ (suc m)) (S₊∙ (suc l))))
--   --                        (inv fromSusp≅fromJoin
--   --                          ((·wh (S₊∙ (suc m)) (S₊∙ (suc n) ⋀∙ S₊∙ (suc l)) g
--   --                          (·wh (S₊∙ (suc n)) (S₊∙ (suc l)) f h
--   --                            ∘∙ SuspSmash→Join∙ (S₊∙ (suc n)) (S₊∙ (suc l)))
--   --                        ∘∙ Jcorrection₂ (S₊∙ (suc n)) (S₊∙ (suc m)) (S₊∙ (suc l)))))))
--   --              ∙ {!!}
--   --              ∙ cong₂ (·Susp (S₊∙ (suc (n + suc (m + suc l)))))
--   --                      (λ _ → (·wh (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l))
--   --                                (·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g
--   --                                   ∘∙ SuspSmash→Join∙ (S₊∙ (suc n)) (S₊∙ (suc m))) h)
--   --                                   ∘∙ ({!!}
--   --                                   ∘∙ {!fromSusp≅fromJoin!}))
--   --                      {!refl!}
--   --              ∙ {!!})

--   -- where
--   -- F1 : Susp∙ (S₊ (suc (n + suc (m + suc l)))) →∙ (join∙ (S₊∙ (suc n)) (S₊∙ (suc m) ⋀∙ S₊∙ (suc l)))
--   -- F1 = ((join→ (idfun (S₊ (suc n)))
--   --       (inv (SphereSmashIso (suc m) (suc l)))
--   --       , (λ _ → inl (idfun (S₊ (suc n)) (ptSn (suc n)))))
--   --      ∘∙
--   --      (sphere→Join (suc n) (suc (m + suc l)) ,
--   --       (λ _ → inl (ptSn (suc n)))))

--   -- F1·Susp : (f g : S₊∙ (suc (suc (n + suc (m + suc l)))) →∙ X)
--   --   → fun fromSusp≅fromJoin (·Susp ((S₊∙ (suc n)) ⋀∙ (S₊∙ (suc m) ⋀∙ S₊∙ (suc l))) (inv fromSusp≅fromJoin {!(·wh (S₊∙ (suc n) ⋀∙ S₊∙ (suc m)) (S₊∙ (suc l))
--   --         (·wh (S₊∙ (suc n)) (S₊∙ (suc m)) f g ∘∙
--   --          SuspSmash→Join∙ (S₊∙ (suc n)) (S₊∙ (suc m)))
--   --         h!}) {!!}) ∘∙ F1 ≡ ·Susp (S₊∙ (suc (n + suc (m + suc l)))) f g
--   -- F1·Susp = {!!}

--   -- lem3 : (join→Sphere (suc m) (suc l) , refl)
--   --        ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))
--   --      ≡ suspFun∙ (fun (SphereSmashIso (suc m) (suc l)))
--   -- lem3 = ΣPathP ((funExt (
--   --   λ { north → refl
--   --     ; south → merid (ptSn (suc m + suc l))
--   --     ; (merid a i) j → lem4 a j i}))
--   --     , sym (rUnit _)
--   --     ∙ cong sym (cong σS (IdR⌣S {n = suc m} {suc l} (ptSn (suc l))) ∙ σS∙))
--   --   where
--   --   lem4 : (t : _)
--   --     → Square (cong (join→Sphere (suc m) (suc l) ∘ SuspSmash→Join) (merid t))
--   --               (merid (fun (SphereSmashIso (suc m) (suc l)) t))
--   --               refl
--   --               (merid (ptSn (suc (m + suc l))))
--   --   lem4 = ⋀→HomogeneousPathP _ (isHomogeneousPath _ _)
--   --     λ x y → (cong-∙∙ (join→Sphere (suc m) (suc l)) (sym (push x (ptSn (suc l)))) (push x y) (sym (push (ptSn (suc m)) y))
--   --       ∙ cong₃ _∙∙_∙∙_
--   --               (cong sym (cong σS (IdL⌣S {n = suc m} {suc l} x)
--   --                         ∙ σS∙))
--   --               refl
--   --               (cong sym (cong σS (IdR⌣S {n = suc m} {suc l} y)
--   --                         ∙ σS∙))
--   --       ∙ sym (rUnit (σS (x ⌣S y))))
--   --       ◁ symP (compPath-filler (merid (x ⌣S y))
--   --                               (sym (merid (ptSn (suc m + suc l)))))

--   -- lem2 : SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l))
--   --      ∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l)))
--   --      ≡ (sphere→Join (suc m) (suc l) , refl)
--   -- lem2 = sym (cong ((sphere→Join (suc m) (suc l) , refl) ∘∙_)
--   --                  (∘∙-assoc _ _ _) -- 
--   --            ∙ sym (∘∙-assoc _ _ _)
--   --            ∙ cong₂ _∘∙_
--   --            (ΣPathP ((funExt (leftInv (IsoSphereJoin (suc m) (suc l))))
--   --                   , (sym (rUnit refl)
--   --   ◁ flipSquare (cong₂ _∙_ refl
--   --       (cong₂ _∙_ (cong-∙∙  (fun SmashJoinIso) refl refl refl
--   --         ∙ sym (rUnit refl)) refl
--   --         ∙ sym (lUnit _))
--   --       ∙ rCancel _)))) refl
--   --            ∙ ∘∙-idʳ _)
--   --      ∙ cong ((sphere→Join (suc m) (suc l) , refl) ∘∙_)
--   --               (cong (_∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l))))
--   --                 lem3)
--   --      ∙ cong₂ _∘∙_ refl (suspFun∙Cancel (SphereSmashIso (suc m) (suc l)))
--   --      ∙ ∘∙-idˡ _

--   -- module _ (g : S₊∙ (suc (suc m)) →∙ X)
--   --          (h : S₊∙ (suc (suc l)) →∙ X) where
--   --   lem1 : [ g ∣ h ] ≡ ((·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h
--   --     ∘∙ SuspSmash→Join∙ (S₊∙ (suc m)) (S₊∙ (suc l)))
--   --       ∘∙ suspFun∙ (inv (SphereSmashIso (suc m) (suc l))))
--   --   lem1 = cong₂ _∘∙_ refl refl
--   --        ∙ cong (·wh (S₊∙ (suc m)) (S₊∙ (suc l)) g h ∘∙_)
--   --               (sym lem2)
--   --        ∙ sym (∘∙-assoc _ _ _)

--   -- rrrr = SuspSmash→Join∙
--   -- module _ (f : S₊∙ (suc (suc n)) →∙ X) (g : S₊∙ (suc (suc m)) →∙ X)
--   --          (h : S₊∙ (suc (suc l)) →∙ X) where
--   --   asd : {!!}
--   --   asd = JacobiR' (S₊∙ (suc n)) (S₊∙ n)
--   --                  (isoToEquiv (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
--   --                  (S₊∙ (suc m)) (S₊∙ m)
--   --                  (isoToEquiv (IsoSucSphereSusp m) , IsoSucSphereSusp∙' m)
--   --                  (S₊∙ (suc l)) (S₊∙ l)
--   --                  (isoToEquiv (IsoSucSphereSusp l) , IsoSucSphereSusp∙' l)
--   --                  f g h
