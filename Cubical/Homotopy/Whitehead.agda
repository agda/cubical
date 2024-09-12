{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.Whitehead where

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
open import Cubical.HITs.SetTruncation

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Join

open Iso
open 3x3-span

-- Whitehead product (main definition)
[_∣_]-pre : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → join∙ (S₊∙ n) (S₊∙ m) →∙ X
fst ([_∣_]-pre {X = X} {n = n} {m = m} f g) (inl x) = pt X
fst ([_∣_]-pre {X = X} {n = n} {m = m} f g) (inr x) = pt X
fst ([_∣_]-pre {n = n} {m = m} f g) (push a b i) =
  (Ω→ g .fst (σS b) ∙ Ω→ f .fst (σS a)) i
snd ([_∣_]-pre {n = n} {m = m} f g) = refl

[_∣_] : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_] {n = n} {m = m} f g =
  [ f ∣ g ]-pre ∘∙ (sphere→Join n m , IsoSphereJoin⁻Pres∙ n m)

-- Whitehead product (as a composition)
joinTo⋁ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
 → join (typ A) (typ B)
 → (Susp (typ A) , north) ⋁ (Susp (typ B) , north)
joinTo⋁ (inl x) = inr north
joinTo⋁ (inr x) = inl north
joinTo⋁ {A = A} {B = B} (push a b i) =
     ((λ i → inr (σ B b i))
  ∙∙ sym (push tt)
  ∙∙ λ i → inl (σ A a i)) i

[_∣_]comp : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_]comp {n = n} {m = m} f g =
    (((f ∘∙ (inv (IsoSucSphereSusp n) , IsoSucSphereSusp∙ n))
  ∨→ (g ∘∙ (inv (IsoSucSphereSusp m) , IsoSucSphereSusp∙ m))
    , cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f)
  ∘∙ ((joinTo⋁ {A = S₊∙ n} {B = S₊∙ m} , sym (push tt))))
  ∘∙ (inv (IsoSphereJoin n m) , IsoSphereJoin⁻Pres∙ n m)

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
        → Square (cong (∨fun f g .fst ∘ joinTo⋁ {A = S₊∙ n} {B = S₊∙ m}) (push a b))
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

-- Homotopy group version
[_∣_]π' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → π' (suc n) X → π' (suc m) X
       → π' (suc (n + m)) X
[_∣_]π' = elim2 (λ _ _ → squash₂) λ f g → ∣ [ f ∣ g ] ∣₂

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

-- Generalised Whitehead products
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C) where

  ·wh : join∙ A B →∙ C
  fst ·wh (inl x) = pt C
  fst ·wh (inr x) = pt C
  fst ·wh (push a b i) = (Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a)) i
  snd ·wh = refl

  -- The generalised Whitehead product vanishes under suspension
  isConst-Susp·w : suspFun∙ (·wh .fst) ≡ const∙ _ _
  isConst-Susp·w = Susp·w∙
                 ∙ cong suspFun∙ (cong fst isConst-const*)
                 ∙ ΣPathP ((suspFunConst (pt C)) , refl)
    where
    const* : join∙ A B →∙ C
    fst const* (inl x) = pt C
    fst const* (inr x) = pt C
    fst const* (push a b i) =
      (Ω→ f .fst (σ A a) ∙ Ω→ g .fst (σ B b)) i
    snd const* = refl

    isConst-const* : const* ≡ const∙ _ _
    fst (isConst-const* i) (inl x) = Ω→ f .fst (σ A x) i
    fst (isConst-const* i) (inr x) = Ω→ g .fst (σ B x) (~ i)
    fst (isConst-const* i) (push a b j) =
      compPath-filler'' (Ω→ f .fst (σ A a)) (Ω→ g .fst (σ B b)) (~ i) j
    snd (isConst-const* i) j =
      (cong (Ω→ f .fst) (rCancel (merid (pt A))) ∙ Ω→ f .snd) j i

    Susp·w : suspFun (fst ·wh) ≡ suspFun (fst const*)
    Susp·w i north = north
    Susp·w i south = south
    Susp·w i (merid (inl x) j) = merid (pt C) j
    Susp·w i (merid (inr x) j) = merid (pt C) j
    Susp·w i (merid (push a b k) j) =
      hcomp (λ r →
        λ {(i = i0) → fill₁ k (~ r) j
         ; (i = i1) → fill₂ k (~ r) j
         ; (j = i0) → north
         ; (j = i1) → merid (pt C) r
         ; (k = i0) → compPath-filler (merid (snd C)) (merid (pt C) ⁻¹) (~ r) j
         ; (k = i1) → compPath-filler (merid (snd C)) (merid (pt C) ⁻¹) (~ r) j})
       (hcomp (λ r →
        λ {(i = i0) → doubleCompPath-filler
                         (sym (rCancel (merid (pt C))))
                         (λ k → fill₁ k i1)
                         (rCancel (merid (pt C))) (~ r) k j
         ; (i = i1) → doubleCompPath-filler
                         (sym (rCancel (merid (pt C))))
                         (λ k → fill₂ k i1)
                         (rCancel (merid (pt C))) (~ r) k j
         ; (j = i0) → north
         ; (j = i1) → north
         ; (k = i0) → rCancel (merid (pt C)) (~ r) j
         ; (k = i1) → rCancel (merid (pt C)) (~ r) j})
           (main i k j))
      where
      F : Ω C .fst → (Ω^ 2) (Susp∙ (fst C)) .fst
      F p = sym (rCancel (merid (pt C)))
         ∙∙ cong (σ C) p
         ∙∙ rCancel (merid (pt C))

      F-hom : (p q : _) → F (p ∙ q) ≡ F p ∙ F q
      F-hom p q =
          cong (sym (rCancel (merid (pt C)))
               ∙∙_∙∙ rCancel (merid (pt C)))
               (cong-∙ (σ C) p q)
        ∙ doubleCompPath≡compPath (sym (rCancel (merid (pt C)))) _ _
        ∙ cong (sym (rCancel (merid (pt C))) ∙_)
               (sym (assoc _ _ _))
        ∙ assoc _ _ _
        ∙ (λ i → (sym (rCancel (merid (pt C)))
                ∙ compPath-filler (cong (σ C) p) (rCancel (merid (pt C))) i)
                ∙ compPath-filler' (sym (rCancel (merid (pt C))))
                                   (cong (σ C) q ∙ rCancel (merid (pt C))) i)
        ∙ cong₂ _∙_ (sym (doubleCompPath≡compPath _ _ _))
                    (sym (doubleCompPath≡compPath _ _ _))

      main : F ((Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a)))
           ≡ F ((Ω→ f .fst (σ A a) ∙ Ω→ g .fst (σ B b)))
      main = F-hom (Ω→ g .fst (σ B b)) (Ω→ f .fst (σ A a))
           ∙ EH 0 _ _
           ∙ sym (F-hom (Ω→ f .fst (σ A a)) (Ω→ g .fst (σ B b)))

      fill₁ : (k : I) → _
      fill₁ k = compPath-filler
                (merid ((Ω→ g .fst (σ B b)
                       ∙ Ω→ f .fst (σ A a)) k))
                (merid (pt C) ⁻¹)

      fill₂ : (k : I) → _
      fill₂ k = compPath-filler
                (merid ((Ω→ f .fst (σ A a)
                       ∙ Ω→ g .fst (σ B b)) k))
                (merid (pt C) ⁻¹)

    Susp·w∙ : suspFun∙ (·wh .fst) ≡ suspFun∙ (fst const*)
    Susp·w∙ = ΣPathP (Susp·w , refl)

-- move
·Suspσ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f g : Susp∙ (typ A) →∙ B)
  → (a : typ A) → cong (·Susp A f g .fst) (σ A a)
                  ≡ Ω→ f .fst (σ A a) ∙ Ω→ g .fst (σ A a)
·Suspσ {A = A} f g a = cong-∙ (·Susp A f g .fst) _ _
  ∙ cong₂ _∙_ refl
          (cong _⁻¹ (cong₂ _∙_ (cong (Ω→ f .fst) (rCancel _) ∙ Ω→ f .snd)
                               (cong (Ω→ g .fst) (rCancel _) ∙ Ω→ g .snd)
                  ∙ sym (rUnit _)))
  ∙ sym (rUnit _)

-- move
open import Cubical.Data.Bool
∙Πσ : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} (f g : S₊∙ (suc n) →∙ A) (t : S₊ n)
  →  Square (cong (fst (∙Π f g)) (σS t))
             (Ω→ f .fst (σS t) ∙ Ω→ g .fst (σS t))
             (snd (∙Π f g)) (snd (∙Π f g))
∙Πσ {A = A} {zero} f g false = refl
∙Πσ {A = A} {zero} f g true =
    rUnit refl
  ∙ cong₂ _∙_ (sym (Ω→ f .snd)) (sym (Ω→ g .snd))
∙Πσ {A = A} {suc n} f g t = ·Suspσ f g t

-- move
·→Ω : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (f g : A →∙ Ω B)
  → A →∙ Ω B
fst (·→Ω f g) x = fst f x ∙ fst g x
snd (·→Ω f g) = cong₂ _∙_ (snd f) (snd g) ∙ sym (rUnit refl)

open import Cubical.Foundations.Pointed.Homogeneous
·Susp≡·→Ω : ∀ {ℓ ℓ'} (A : Pointed ℓ) {B : Pointed ℓ'}
  (f g : Susp∙ (typ A) →∙ Ω B)
  → ·Susp A f g ≡ ·→Ω f g
·Susp≡·→Ω A {B = B} f g =
  →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ { north → rUnit refl
                       ∙ cong₂ _∙_ (sym (snd f)) (sym (snd g))
              ; south → rUnit refl
                       ∙ cong₂ _∙_ (snd f ⁻¹ ∙ cong (fst f) (merid (pt A)))
                                   (snd g ⁻¹ ∙ cong (fst g) (merid (pt A)))
              ; (merid a i) j →
                (cong₂ _∙_ (cong (sym (snd f) ∙∙_∙∙ snd f) (cong-∙ (fst f) _ _))
                           (cong (sym (snd g) ∙∙_∙∙ snd g) (cong-∙ (fst g) _ _))
                ◁ lem B _ (sym (snd f)) _
                      (cong (fst f) (merid a))
                      (cong (fst f) (merid (pt A)))
                      _ (sym (snd g)) _
                      (cong (fst g) (merid a))
                      (cong (fst g) (merid (pt A)))) j i})
  where
  open import Cubical.Foundations.Path
  lem : ∀ {ℓ} (A : Pointed ℓ) (⋆f : Ω A .fst) (sndf : refl ≡ ⋆f)
              (⋆fs : Ω A .fst) (mfa mfb : ⋆f ≡ ⋆fs)
              (⋆g : Ω A .fst) (sndg : refl ≡ ⋆g)
              (⋆gs : Ω A .fst) (mga mgb : ⋆g ≡ ⋆gs)
        → Square ((sndf ∙∙ mfa ∙ mfb ⁻¹ ∙∙ sym sndf)
                  ∙ (sndg ∙∙ mga ∙ mgb ⁻¹ ∙∙ sym sndg))
                 (cong₂ _∙_ mfa mga)
                 (rUnit refl ∙ cong₂ _∙_ sndf sndg)
                 (rUnit refl ∙ cong₂ _∙_ (sndf ∙ mfb) (sndg ∙ mgb))
  lem A = J> (J> λ mfb → J> (J>
    λ mgb → cong₂ _∙_ (sym (rUnit _) ∙ sym (lUnit (mfb ⁻¹)))
                       (sym (rUnit _) ∙ sym (lUnit (mgb ⁻¹)))
          ◁ flipSquare (sym (rUnit (rUnit refl))
          ◁ (flipSquare (sym (symDistr mgb mfb)
          ◁ flipSquare (compPath-filler' (mgb ∙ mfb) (rUnit refl)))
          ▷ (cong (_∙ rUnit refl) (EH 0 mgb mfb)
             ∙ lUnit _
            ∙ (λ j → (λ i → rUnit refl (i ∧ j))
                    ∙ (cong (λ x → rUnit x j) mfb
                    ∙ cong (λ x → lUnit x j) mgb)
                    ∙ λ i → rUnit refl (i ∨ j))
            ∙ cong (rUnit refl ∙_)
              (sym (rUnit _)
              ∙ sym (cong₂Funct _∙_ mfb mgb)
            ∙ (λ j → cong₂ _∙_ (lUnit mfb j) (lUnit mgb j))))))))

Susp·→Ωcomm : ∀ {ℓ ℓ'} (A : Pointed ℓ) {B : Pointed ℓ'}
  (f g : Susp∙ (typ A) →∙ Ω B) → ·→Ω f g ≡ ·→Ω g f
Susp·→Ωcomm A {B = B} f g = isoInvInjective ΩSuspAdjointIso _ _
  (cong fromSusp→toΩ (·Susp≡·→Ω _ f g ⁻¹)
  ∙∙ help
  ∙∙ cong fromSusp→toΩ (·Susp≡·→Ω _ g f))
  where
  help : Iso.inv ΩSuspAdjointIso (·Susp _ f g)
       ≡ Iso.inv ΩSuspAdjointIso (·Susp _ g f)
  help = →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ x → sym (rUnit _)
                ∙ ·Suspσ f g x
                ∙ EH 0 _ _
                ∙ sym (·Suspσ g f x)
                ∙ rUnit _)

·SuspComm : ∀ {ℓ ℓ'} (A : Pointed ℓ) {B : Pointed ℓ'}
  (f g : Susp∙ (Susp (typ A)) →∙ B)
  → ·Susp (Susp∙ (typ A)) f g ≡ ·Susp (Susp∙ (typ A)) g f
·SuspComm A {B = B} f g = isoInvInjective ΩSuspAdjointIso _ _ cool
  where
  cool : Iso.inv ΩSuspAdjointIso (·Susp (Susp∙ (typ A)) f g)
       ≡ Iso.inv ΩSuspAdjointIso (·Susp (Susp∙ (typ A)) g f)
  cool = →∙Homogeneous≡ (isHomogeneousPath _ _)
    (funExt λ x → sym (rUnit _)
                ∙ ·Suspσ f g x
                ∙ funExt⁻ (cong fst (Susp·→Ωcomm _
                           (Iso.inv ΩSuspAdjointIso f) (Iso.inv ΩSuspAdjointIso g))) x
                ∙ sym (·Suspσ g f x)
                ∙ rUnit _)

EH-ΠΩ : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} (f g : S₊∙ (suc n) →∙ Ω A)
     → ·→Ω f g ≡ ·→Ω g f
EH-ΠΩ {A = A} {n = n} =
  subst (λ T → (f g : T →∙ Ω A) → ·→Ω f g ≡ ·→Ω g f)
        (ua∙ (isoToEquiv (invIso (IsoSucSphereSusp n))) (IsoSucSphereSusp∙ n))
        (Susp·→Ωcomm (S₊∙ n))

cong·wh-ℓ* : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
     (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
     (a : _) (b : _)
  → (cong (fst (·wh A B f g)) (ℓ* A B a b))
  ≡ ((Ω→ f .fst (σ A a) ⁻¹)
  ∙∙ (Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a))
  ∙∙ (Ω→ g .fst (σ B b) ⁻¹))
cong·wh-ℓ* {A = A} {B = B} f g a b =
    cong-∙ (fst (·wh A B f g)) _ _
  ∙ cong₂ _∙_ (cong₂ _∙_ gp fp
            ∙ sym (rUnit _))
            (cong-∙∙ (fst (·wh A B f g)) _ _ _
          ∙ cong₃ _∙∙_∙∙_
              (cong _⁻¹ (cong₂ _∙_ gp refl ∙ sym (lUnit _)))
              refl
              (cong _⁻¹ (cong₂ _∙_ refl fp ∙ sym (rUnit _))))
  ∙ sym (lUnit _)
  where
  fp = cong (Ω→ f .fst) (rCancel _) ∙ Ω→ f .snd
  gp = cong (Ω→ g .fst) (rCancel _) ∙ Ω→ g .snd

-- S


module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (Susp (typ A)) →∙ C)
         (g : Susp∙ (Susp (typ B)) →∙ C)
  where
  private
    σΣA = σ (Susp∙ (typ A))
    σΣB = σ (Susp∙ (typ B))
    
    Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid north)) ∙ Ω→ f .snd
    Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd
    Ω→-g∙ = cong (Ω→ (-Susp (Susp∙ (typ B)) g) .fst) (rCancel (merid north))
          ∙ Ω→ (-Susp (Susp∙ (typ B)) g) .snd

    wh' : join∙ (Susp∙ (typ A)) (Susp∙ (typ B)) →∙ C
    wh' = ·wh (Susp∙ (typ B)) (Susp∙ (typ A)) (-Susp _ g) f
                           ∘∙ (Iso.fun join-comm , push north north ⁻¹)


-- -*²
  anticomm : -* (·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g)
           ≡  (·wh (Susp∙ (typ B)) (Susp∙ (typ A)) (-Susp (Susp∙ (typ B)) g) f
             ∘∙ (Iso.fun join-comm , push north north ⁻¹))
  fst (anticomm i) (inl x) = Ω→ f .fst (σΣA x) i
  fst (anticomm i) (inr x) = Ω→ g .fst (σΣB x) i
  fst (anticomm i) (push a b i₁) = l i i₁
    where
    x = Ω→ f .fst (σΣA a)
    y = Ω→ g .fst (σΣB b)

    fun1 fun2 : Susp∙ (typ A) →∙ Ω C
    fst fun1 a = y ∙ (Ω→ f .fst (σΣA a) ⁻¹) ∙ y ⁻¹
    snd fun1 =
      cong (y ∙_)
        (cong (_∙ y ⁻¹)
          (cong sym ((Ω→ f ∘∙ toSuspPointed _) .snd))
                    ∙ sym (lUnit _) )
      ∙ rCancel y
    fun2 = Ω→ f ∘∙ toSuspPointed _

    l : Square (cong (fst (-* ((·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g)))) (push a b))
               (cong (fst wh') (push a b))
               x y
    l = (λ _ → Ω→ (·wh (Susp∙ (typ A)) (Susp∙ (typ B))  f g) .fst (ℓ* (_ , north) (_ , north) a b) ⁻¹)
      ∙ sym (rUnit _)
      ∙ cong sym (cong·wh-ℓ* f g a b)
      ∙ cong₃ _∙∙_∙∙_ refl (symDistr _ _) refl
      ∙ doubleCompPath≡compPath _ _ _
      ∙ assoc _ _ _
      ∙ (λ i → fst (Susp·→Ωcomm _ fun1 fun2 i) a)
      ∙ cong (x ∙_) (assoc _ _ _)
      ∙ sym (doubleCompPath≡compPath _ _ _)
      ◁ symP (doubleCompPath-filler x (y ∙ x ⁻¹) (y ⁻¹))
      ▷ cong (_∙ x ⁻¹) (cong sym (sym
               (cong-∙ (fst (-Susp (Susp (typ B) , north) g))
                 (merid b)
                 (sym (merid north))
            ∙ cong₂ _∙_ refl Ω→g∙ ∙ sym (rUnit _)) ∙ rUnit _))
      ∙ compPath≡compPath' _ _
  snd (anticomm i) j = lem i j
    where
    lem : Square refl (snd wh') (Ω→ f .fst (σΣA north)) refl
    lem = flipSquare Ω→f∙
        ▷ (cong sym (rUnit refl ∙ cong₂ _∙_ (sym Ω→f∙) (sym (Ω→-g∙))) ∙ rUnit _)

  {-                     [f ∶ g]
  (Susp A) * (Susp B) ----------------->  C
           |                              ^
           |                              | 
           |                              |
      flip |                              | [-g ∶ f]
           |                              |
           v                              |
  (Susp B) * (Susp C) ----------> (Susp B) * (Susp C)
                          -
  -}

  aad = {!·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g!}


  WhiteheadProdComm : ·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g
                    ≡ -* (·wh (Susp∙ (typ B)) (Susp∙ (typ A)) (-Susp (Susp∙ (typ B)) g) f
                      ∘∙ (Iso.fun join-comm , push north north ⁻¹))
  WhiteheadProdComm = sym (-*² _) ∙ cong -* anticomm

-- Bilinearity of generalised whitehead product
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f g : Susp∙ (Susp (typ A)) →∙ C) (h : Susp∙ (typ B) →∙ C) where
  private
    σΣA = σ (Susp∙ (typ A))
    Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid north)) ∙ Ω→ f .snd
    Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd

  WhiteheadProdBilinₗ : ·wh (Susp∙ (typ A)) B (·Susp (Susp∙ (typ A)) f g) h
                     ≡ (·wh (Susp∙ (typ A)) B f h) +* (·wh (Susp∙ (typ A)) B g h)
  fst (WhiteheadProdBilinₗ i) (inl x) =
    (Ω→ g .fst (σΣA x) ∙ Ω→ f .fst (σΣA x)) i
  fst (WhiteheadProdBilinₗ i) (inr x) = Ω→ h .fst (σ B x) (~ i)
  fst (WhiteheadProdBilinₗ i) (push a b j) = main i j
    where
    x = Ω→ f .fst (σΣA a)
    y = Ω→ g .fst (σΣA a)
    z = Ω→ h .fst (σ B b)

    fun1 fun2 fun3 : Susp∙ (typ A) →∙ Ω C
    fst fun1 a = z ⁻¹ ∙ (Ω→ g .fst (σΣA a)) ⁻¹ ∙ z
    snd fun1 = cong (z ⁻¹ ∙_) (cong (_∙ z) (cong sym Ω→g∙)
                            ∙ sym (lUnit z))
             ∙ lCancel z
    fst fun2 a = ((z ∙ Ω→ f .fst (σΣA a)) ∙ Ω→ g .fst (σΣA a)) ∙ z ⁻¹
    snd fun2 = cong (_∙ z ⁻¹)
                   (cong₂ _∙_ (cong (z ∙_)
                               Ω→f∙ ∙ sym (rUnit _))
                               Ω→g∙
                 ∙ sym (rUnit _))
            ∙ rCancel z
    fun3 = Ω→ g ∘∙ toSuspPointed (Susp∙ (typ A))

    lem : y ⁻¹ ∙ ((z ∙ x) ∙ y) ∙ z ⁻¹ ≡ (z ∙ x ∙ z ⁻¹) ∙ ((y ⁻¹ ∙ z) ∙ y) ∙ z ⁻¹
    lem = (sym (funExt⁻ (cong fst
                  (Susp·→Ωcomm A fun2 ((sym , refl) ∘∙ fun3))) a)
        ∙ sym (assoc _ _ _)
        ∙ sym (assoc _ _ _))
        ∙ (λ j → (z ∙ x) ∙ y ∙ z ⁻¹ ∙ (rUnit (y ⁻¹) j))
        ∙ rUnit _
        ∙ (λ i → ((z ∙ x) ∙ y ∙ z ⁻¹ ∙ y ⁻¹
                 ∙ λ j → z (j ∧ i)) ∙ λ j → z (~ j ∧ i))
        ∙ cong (_∙ z ⁻¹)
        (cong ((z ∙ x) ∙_)
            (sym (funExt⁻ (cong fst (Susp·→Ωcomm A fun1 fun3)) a)
           ∙ sym (assoc _ _ _))
        ∙ assoc _ _ _
        ∙ cong₂ _∙_ (sym (assoc z x (z ⁻¹)))
                    refl)
        ∙ sym (assoc _ _ _)

    main : Square (cong (·wh (Susp∙ (typ A)) B
                          (·Susp (Susp∙ (typ A)) f g) h .fst) (push a b))
                  (cong (((·wh (Susp∙ (typ A)) B f h)
                       +* (·wh (Susp∙ (typ A)) B g h)) .fst) (push a b))
                  (y ∙ x) (z ⁻¹)
    main = cong₂ _∙_ refl (sym (rUnit _) ∙ ·Suspσ f g a)
        ∙ assoc z x y
       ◁ doubleCompPath-filler (sym (y ∙ x)) ((z ∙ x) ∙ y) (z ⁻¹)
       ▷ (doubleCompPath≡compPath _ _ _
        ∙ cong₂ _∙_ (symDistr y x) refl
        ∙ sym (assoc (x ⁻¹) (y ⁻¹) _)
        ∙ cong (x ⁻¹ ∙_) lem
        ∙ assoc (x ⁻¹) (z ∙ x ∙ z ⁻¹) (((y ⁻¹ ∙ z) ∙ y) ∙ z ⁻¹)
         ∙ cong₂ _∙_ (cong (x ⁻¹ ∙_) (assoc z x (z ⁻¹)))
                     (cong (_∙ z ⁻¹) (sym (assoc (y ⁻¹) z y))
                     ∙ sym (assoc (y ⁻¹) (z ∙ y) _))
         ∙ sym (cong₂ _∙_ (sym (rUnit _) ∙ cong·wh-ℓ* f h a b
                          ∙ doubleCompPath≡compPath _ _ _)
                          (sym (rUnit _) ∙ cong·wh-ℓ* g h a b
                          ∙ doubleCompPath≡compPath _ _ _)))

  snd (WhiteheadProdBilinₗ i) j = lem j i
    where    
    lem : Ω→ g .fst (σΣA north) ∙ Ω→ f .fst (σΣA north)
       ≡ refl
    lem = cong₂ _∙_ Ω→g∙ Ω→f∙
        ∙ sym (rUnit refl)
