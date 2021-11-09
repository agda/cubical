{-# OPTIONS --safe #-}
module Cubical.Homotopy.Whitehead where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Data.Bool
open import Cubical.Data.Unit


open import Cubical.HITs.Join
open import Cubical.HITs.Sn
open import Cubical.HITs.Wedge
private
  variable
    ℓ : Level
    A B : Pointed ℓ

join-elim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
         → {P : join A B → Type ℓ''}
         → (l : (a : A) → P (inl a))
         → (r : (b : B) → P (inr b))
         → ((a : A) (b : B) → PathP (λ i → P (push a b i)) (l a) (r b))
         → (x : join A B) → P x
join-elim l r p (inl x) = l x
join-elim l r p (inr x) = r x
join-elim l r p (push a b i) = p a b i

φ : (A : Pointed ℓ) (a : typ A) → Path (Susp (typ A)) north north
φ A a = merid a ∙ sym (merid (pt A))

W : join (typ A) (typ B) → (Susp (typ A) , north) ⋁ (Susp (typ B) , north)
W (inl x) = inr north
W (inr x) = inl north
W {A = A} {B = B} (push a b i) =
     ((λ i → inr (φ B b i))
  ∙∙ sym (push tt)
  ∙∙ λ i → inl (φ A a i)) i

open 3x3-span
open Iso

module _ (A B : Type) (a₀ : A) (b₀ : B) where
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
  H11 whitehead3x3 (a , _) = merid a
  H13 whitehead3x3 _ = refl
  H31 whitehead3x3 _ = refl
  H33 whitehead3x3 _ = refl

  A∨B = (Susp A , north) ⋁ (Susp B , north)

  φB = φ (B , b₀)
  φA = φ (A , a₀)

  A0□→A∨B : A0□ whitehead3x3 → A∨B
  A0□→A∨B (inl x) = inl x
  A0□→A∨B (inr x) = inr north
  A0□→A∨B (push a i) = (push tt ∙ λ i → inr (φB a i)) i -- (~ i)

  A∨B→A0□ : A∨B → A0□ whitehead3x3
  A∨B→A0□ (inl x) = inl x
  A∨B→A0□ (inr north) = inl north
  A∨B→A0□ (inr south) = inl north
  A∨B→A0□ (inr (merid b i)) = (push b ∙ sym (push b₀)) i -- b₀ -> b
  A∨B→A0□ (push a i) = inl north

  firstRow≡Susp⋁ : Iso (A0□ whitehead3x3) A∨B
  fun firstRow≡Susp⋁ = A0□→A∨B
  inv firstRow≡Susp⋁ = A∨B→A0□
  rightInv firstRow≡Susp⋁ (inl x) = refl
  rightInv firstRow≡Susp⋁ (inr north) = push tt
  rightInv firstRow≡Susp⋁ (inr south) = push tt ∙ λ i → inr (merid b₀ i)
  rightInv firstRow≡Susp⋁ (inr (merid b i)) = flipSquare help i
    where
    lem : cong A0□→A∨B (push b) ∙ sym (cong A0□→A∨B (push b₀))
        ≡ push tt ∙∙ (λ i → inr ((merid b ∙ sym (merid b₀)) i)) ∙∙ sym (push tt)
    lem = (λ k → (push tt ∙ (λ i → inr ((merid b ∙ sym (merid b₀)) i)))
        ∙ sym ((((λ k → push tt ∙ (λ i → inr (rCancel (merid b₀) k i)))
                ∙ sym (rUnit (push tt))) k)))
        ∙∙ sym (assoc _ _ _)
        ∙∙ λ i j → hcomp (λ k → λ { (i = i0) → compPath-filler' (push tt) (compPath-filler (λ i₂ → inr ((merid b ∙ (λ i₃ → merid b₀ (~ i₃))) i₂)) (sym (push tt)) k) k j
                                    ; (j = i0) → push tt (~ k)
                                    ; (j = i1) → push tt (~ k)})
                          (inr ((merid b ∙ (λ i₃ → merid b₀ (~ i₃))) j))

    help : PathP (λ i → Path A∨B (push tt i) ((push tt ∙ λ i → inr (merid b₀ i)) i))
                 (cong (A0□→A∨B) (cong (A∨B→A0□) λ i → inr (merid b i)))
                 λ i → inr (merid b i)
    help = (cong-∙ A0□→A∨B (push b) (sym (push b₀)) ∙ lem)
         ◁ λ i j → hcomp (λ k → λ { (i = i1) → inr (merid b j)
                                    ; (j = i0) → push tt (i ∨ ~ k)
                                    ; (j = i1) → compPath-filler' (push tt) (λ i₂ → inr (merid b₀ i₂)) k i})
                          (inr (compPath-filler (merid b) (sym (merid b₀)) (~ i) j))
  rightInv firstRow≡Susp⋁ (push a i) j = push tt (j ∧ i)
  leftInv firstRow≡Susp⋁ (inl x) = refl
  leftInv firstRow≡Susp⋁ (inr x) = push b₀
  leftInv firstRow≡Susp⋁ (push b i) j = help j i
    where
    lem : cong (inv firstRow≡Susp⋁) (push tt ∙ (λ i₁ → inr (φB b i₁)))
        ≡ push b ∙ sym (push b₀)
    lem = cong-∙ (inv firstRow≡Susp⋁) (push tt) (λ i₁ → inr (φB b i₁))
       ∙∙ sym (lUnit _)
       ∙∙ cong-∙ ((inv firstRow≡Susp⋁ ∘ inr)) (merid b) (sym (merid b₀))
       ∙∙ cong ((push b ∙ sym (push b₀)) ∙_) (cong sym (rCancel (push b₀)))
       ∙∙ sym (rUnit _)

    help : PathP (λ i → Path (A0□ whitehead3x3) (inl north) (push b₀ i))
                 (λ i → inv firstRow≡Susp⋁ (fun firstRow≡Susp⋁ (push b i)))
                 (push b)
    help =
        lem
      ◁ λ i j → compPath-filler (push b) (sym (push b₀)) (~ i) j

  2ndRow≡join : Iso (A2□ whitehead3x3) (join A B)
  fun 2ndRow≡join (inl x) = inr x
  fun 2ndRow≡join (inr x) = inl x
  fun 2ndRow≡join (push (a , b) i) = push a b (~ i)
  inv 2ndRow≡join (inl x) = inr x
  inv 2ndRow≡join (inr x) = inl x
  inv 2ndRow≡join (push a b i) = push (a , b) (~ i)
  rightInv 2ndRow≡join (inl x) = refl
  rightInv 2ndRow≡join (inr x) = refl
  rightInv 2ndRow≡join (push a b i) = refl
  leftInv 2ndRow≡join (inl x) = refl
  leftInv 2ndRow≡join (inr x) = refl
  leftInv 2ndRow≡join (push a i) = refl

  isContr-3rdRow : isContr (A4□ whitehead3x3)
  fst isContr-3rdRow = inr tt
  snd isContr-3rdRow (inl x) = sym (push x)
  snd isContr-3rdRow (inr x) = refl
  snd isContr-3rdRow (push a i) j = push a (i ∨ ~ j)

  isContr-3rdRow' : A4□ whitehead3x3 ≃ Unit
  isContr-3rdRow' = isContr→≃Unit isContr-3rdRow

  1stColumn≡SuspA : Iso (A□0 whitehead3x3) (Susp A)
  fun 1stColumn≡SuspA (inl x) = x
  fun 1stColumn≡SuspA (inr x) = north
  fun 1stColumn≡SuspA (push a i) = merid a₀ (~ i)
  inv 1stColumn≡SuspA x = inl x
  rightInv 1stColumn≡SuspA x = refl
  leftInv 1stColumn≡SuspA (inl x) = refl
  leftInv 1stColumn≡SuspA (inr x) = (λ i → inl (merid a₀ i)) ∙ push x
  leftInv 1stColumn≡SuspA (push a i) j =
    hcomp (λ k → λ { (i = i0) → inl (merid a₀ (k ∨ j))
                    ; (i = i1) → compPath-filler
                                   (λ i₁ → inl (merid a₀ i₁))
                                   (push (idfun B a)) k j
                    ; (j = i0) → inl (merid a₀ (~ i ∧ k))
                    ; (j = i1) → push a (i ∧ k)})
          (inl (merid a₀ j))

  2rdColumn≡SuspA : Iso (A□2 whitehead3x3) (Susp A × B)
  fun 2rdColumn≡SuspA (inl x) = north , x
  fun 2rdColumn≡SuspA (inr x) = south , x
  fun 2rdColumn≡SuspA (push a i) = merid (fst a) i , (snd a)
  inv 2rdColumn≡SuspA (north , y) = inl y
  inv 2rdColumn≡SuspA (south , y) = inr y
  inv 2rdColumn≡SuspA (merid a i , y) = push (a , y) i
  rightInv 2rdColumn≡SuspA (north , snd₁) = refl
  rightInv 2rdColumn≡SuspA (south , snd₁) = refl
  rightInv 2rdColumn≡SuspA (merid a i , snd₁) = refl
  leftInv 2rdColumn≡SuspA (inl x) = refl
  leftInv 2rdColumn≡SuspA (inr x) = refl
  leftInv 2rdColumn≡SuspA (push a i) = refl

  3rdColumn≡SuspA : Iso (A□4 whitehead3x3) (Susp A)
  fun 3rdColumn≡SuspA (inl x) = north
  fun 3rdColumn≡SuspA (inr x) = south
  fun 3rdColumn≡SuspA (push a i) = merid a i
  inv 3rdColumn≡SuspA north = inl tt
  inv 3rdColumn≡SuspA south = inr tt
  inv 3rdColumn≡SuspA (merid a i) = push a i
  rightInv 3rdColumn≡SuspA north = refl
  rightInv 3rdColumn≡SuspA south = refl
  rightInv 3rdColumn≡SuspA (merid a i) = refl
  leftInv 3rdColumn≡SuspA (inl x) = refl
  leftInv 3rdColumn≡SuspA (inr x) = refl
  leftInv 3rdColumn≡SuspA (push a i) = refl

  module P {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (AIso : A₁ ≃ A₂) (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂)
               (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
               (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
               (id1 : (fst BIso) ∘ f₁ ≡ f₂ ∘ (fst AIso))
               (id2 : (fst CIso) ∘ g₁ ≡ g₂ ∘ (fst AIso))
   where
   F' : Pushout f₁ g₁ → Pushout f₂ g₂
   F' (inl x) = inl (fst BIso x)
   F' (inr x) = inr (fst CIso x)
   F' (push a i) =
     ((λ i → inl (funExt⁻ id1 a i))
      ∙∙ push (fst AIso a)
      ∙∙ λ i → inr (sym (funExt⁻ id2 a) i)) i

   G' : Pushout f₂ g₂ → Pushout f₁ g₁
   G' (inl x) = inl (invEq BIso x)
   G' (inr x) = inr (invEq CIso x)
   G' (push a i) =
     ((λ i → inl ((sym (cong (invEq BIso) (funExt⁻ id1 (invEq AIso a)
                    ∙ cong f₂ (secEq AIso a)))
                    ∙ retEq BIso (f₁ (invEq AIso a))) i))
      ∙∙ push (invEq AIso a)
      ∙∙ λ i → inr (((sym (retEq CIso (g₁ (invEq AIso a)))
                   ∙ (cong (invEq CIso) ((funExt⁻ id2 (invEq AIso a)))))
                   ∙ cong (invEq CIso) (cong g₂ (secEq AIso a))) i)) i


  cType₁ : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (AIso : A₁ ≃ A₂) (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂)
         → (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
            (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
         → (id1 : (fst BIso) ∘ f₁ ≡ f₂ ∘ (fst AIso))
            (id2 : (fst CIso) ∘ g₁ ≡ g₂ ∘ (fst AIso))
         → Type _
  cType₁ AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2 =
      ((x : _) → P.F' AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2
                   (P.G' AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2 x) ≡ x)
    × ((x : _) → P.G' AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2
                   (P.F' AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2 x) ≡ x)

  cType : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (AIso : A₁ ≃ A₂) (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂)
          → Type _
  cType {A₁ = A₁} {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂}
         AIso BIso CIso =
    (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
               (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
               (id1 : (fst BIso) ∘ f₁ ≡ f₂ ∘ (fst AIso))
               (id2 : (fst CIso) ∘ g₁ ≡ g₂ ∘ (fst AIso))
               → cType₁ AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2

  F-G-cancel : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (AIso : A₁ ≃ A₂) (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂)
             → cType AIso BIso CIso
  F-G-cancel {A₁ = A₁} {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂} =
    EquivJ (λ A₁ AIso → (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂) →
      cType AIso BIso CIso)
      (EquivJ (λ B₁ BIso → (CIso : C₁ ≃ C₂) →
      cType (idEquiv A₂) BIso CIso)
        (EquivJ (λ C₁ CIso → cType (idEquiv A₂) (idEquiv B₂) CIso)
          λ f₁ g₁ f₂ g₂
            → J (λ f₂ id1 → (id2 : g₁ ≡ g₂)
                          → cType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                                    f₁ g₁ f₂ g₂ id1 id2)
                 (J (λ g₂ id2 → cType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                                        f₁ g₁ f₁ g₂ refl id2)
                    (postJ f₁ g₁))))

    where
    postJ : (f₁ : A₂ → B₂) (g₁ : A₂ → C₂)
      → cType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                 f₁ g₁ f₁ g₁ refl refl
    postJ f₁ g₁ = help , help₂
      where
      refl-lem : ∀ {ℓ} {A : Type ℓ} (x : A) → (refl {x = x} ∙ refl) ∙ refl ≡ refl
      refl-lem x = sym (rUnit _) ∙ sym (rUnit _)

      FF = P.F' (idEquiv A₂) (idEquiv B₂) (idEquiv C₂) f₁ g₁ f₁ g₁ refl refl
      GG = P.G' (idEquiv A₂) (idEquiv B₂) (idEquiv C₂) f₁ g₁ f₁ g₁ refl refl

      help : (x : Pushout f₁ g₁) → FF (GG x) ≡ x
      help (inl x) = refl
      help (inr x) = refl
      help (push a i) j = hh j i
        where
        hh : Path (Path (Pushout f₁ g₁) (inl (f₁ a)) (inr (g₁ a)))
                  (cong FF ((λ i → inl (((refl ∙ refl) ∙ (refl {x = f₁ a})) i ))
                        ∙∙ push {f = f₁} {g = g₁} a
                        ∙∙ λ i → inr (((refl ∙ refl) ∙ (refl {x = g₁ a})) i)))
                  (push a)
        hh = (λ i → cong FF ((λ j → inl (refl-lem (f₁ a) i j))
                           ∙∙ push a
                           ∙∙ λ j → inr (refl-lem (g₁ a) i j)))
          ∙∙ cong (cong FF) (sym (rUnit (push a)))
          ∙∙ sym (rUnit (push a))

      help₂ : (x : _) → GG (FF x) ≡ x
      help₂ (inl x) = refl
      help₂ (inr x) = refl
      help₂ (push a i) j = hh j i
        where
        hh : cong GG (refl ∙∙ push a ∙∙ refl) ≡ push a
        hh = cong (cong GG) (sym (rUnit (push a)))
          ∙∙ (λ i → ((λ j → inl (refl-lem (f₁ a) i j))
                   ∙∙ push a
                   ∙∙ λ j → inr (refl-lem (g₁ a) i j)))
          ∙∙ sym (rUnit (push a))

  pushoutIso : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
               (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
               (AIso : A₁ ≃ A₂) (BIso : B₁ ≃ B₂) (CIso : C₁ ≃ C₂)
             → (fst BIso ∘ f₁ ≡ f₂ ∘ fst AIso)
             → (id2 : fst CIso ∘ g₁ ≡ g₂ ∘ fst AIso)
             → Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
  pushoutIso f₁ g₁ f₂ g₂ AIso BIso CIso id1 id2 = theIso
    where
    module P' = P AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2

    l-r-cancel = F-G-cancel AIso BIso CIso f₁ g₁ f₂ g₂ id1 id2

    theIso : Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
    fun theIso = P'.F'
    inv theIso = P'.G'
    rightInv theIso = fst l-r-cancel
    leftInv theIso = snd (l-r-cancel)

  Pushout-fst-fst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                  → (b₀ : B)
                  → Iso (Pushout {A = A × B} fst fst) A
  fun (Pushout-fst-fst b₀) (inl x) = x
  fun (Pushout-fst-fst b₀) (inr x) = x
  fun (Pushout-fst-fst b₀) (push a i) = fst a
  inv (Pushout-fst-fst b₀) x = inl x
  rightInv (Pushout-fst-fst b₀) x = refl
  leftInv (Pushout-fst-fst b₀) (inl x) = refl
  leftInv (Pushout-fst-fst b₀) (inr x) = push (x , b₀)
  leftInv (Pushout-fst-fst b₀) (push (a , b) i) j = {!!}

  PushoutPushout : Iso (Pushout {A = Susp A × B} fst fst)
                       (Susp A × Susp B)
  PushoutPushout = theIso
    where
    F : Pushout {A = Susp A × B} fst fst
     → Susp A × Susp B
    F (inl x) = x , north
    F (inr x) = x , north
    F (push (x , b) i) = x , φB b i

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
                   (cong G (λ i → a , φB b i))
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

  PushoutColumn₁ : Iso (A□○ whitehead3x3) (Pushout {A = Susp A × B} fst fst)
  PushoutColumn₁ =
    pushoutIso _ _ fst fst
      (isoToEquiv 2rdColumn≡SuspA)
      (isoToEquiv 1stColumn≡SuspA)
      (isoToEquiv 3rdColumn≡SuspA)
      (funExt (λ { (inl x) → refl
                 ; (inr x) → merid a₀
                 ; (push a i) j → help₁ a j i}))
      (funExt λ { (inl x) → refl
                ; (inr x) → refl
                ; (push a i) j
                  → fun 3rdColumn≡SuspA (rUnit (push (fst a)) (~ j) i)})
    where
    help₁ : (a : A × B)
      → PathP (λ i → north ≡ merid a₀ i)
               (cong (fun 1stColumn≡SuspA)
                 (cong (f□1 whitehead3x3) (push a)))
               (merid (fst a))
    help₁ a =
        (cong-∙∙ (fun 1stColumn≡SuspA)
                 (λ i → inl (merid (fst a) i))
                 (push (snd a))
                 refl)
      ◁ (λ i j → hcomp (λ k → λ {(i = i1) → merid (fst a) (j ∨ ~ k)
                                 ; (j = i0) → merid (fst a) (~ k)
                                 ; (j = i1) → merid a₀ i})
                        (merid a₀ (i ∨ ~ j)))

  PushoutColumn : Iso (A□○ whitehead3x3) (Susp A × Susp B)
  PushoutColumn = compIso PushoutColumn₁ PushoutPushout

  W-AB = W {A = (A , a₀)} {B = (B , b₀)}

  PushoutRows₁ : Iso (A○□ whitehead3x3) (Pushout W-AB λ _ → tt)
  PushoutRows₁ =
    pushoutIso _ _
      W-AB (λ _ → tt)
      (isoToEquiv 2ndRow≡join) (isoToEquiv firstRow≡Susp⋁)
      isContr-3rdRow'
      (funExt {!!})
      λ _ _ → tt
    where
    hej : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (l : x ≡ x) (r : y ≡ y)
        → PathP (λ i → p i ≡ p (~ i))
                 (l ∙∙ p ∙∙ r)
                 (sym r ∙∙ sym p ∙∙ sym l)
    hej {x = x} =
      J (λ y p → (l : x ≡ x) (r : y ≡ y)
        → PathP (λ i → p i ≡ p (~ i))
                 (l ∙∙ p ∙∙ r)
                 (sym r ∙∙ sym p ∙∙ sym l))
        λ l r → {!!}

    h : (x : A2□ whitehead3x3)
      → A0□→A∨B (f1□ whitehead3x3 x) ≡ W-AB (fun 2ndRow≡join x)
    h (inl x) = (λ i → inl (merid a₀ (~ i)))
    h (inr x) = refl
    h (push (a , b) i) j = {!!} -- help j i

--       where
--       lem : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
--                                 ((inl (merid a₀ (~ i))))
--                                 (inr north))
--                   ((λ i → inl (merid a (~ i))) ∙ push tt ∙ (λ i → inr (φB b i)))
--                   (((λ i → inl (φA a (~ i))) ∙∙ (push tt) ∙∙ (λ i → inr (φB b (~ i)))))
--       lem i j = {!!}

--       help : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
--                                 ((inl (merid a₀ (~ i))))
--                                 (inr north))
--                    (cong A0□→A∨B (cong (f1□ whitehead3x3) (push (a , b))))
--                    (cong W-AB (cong (fun 2ndRow≡join) (push (a , b))))
--       help =
--           (cong-∙∙ A0□→A∨B (λ i → inl (merid a (~ i))) (push b) refl
--           ∙ (λ i → (λ i → inl (merid a (~ i))) ∙∙ push tt ∙ (λ i → inr (φB b i)) ∙∙ refl)
--           ∙ sym (compPath≡compPath' ((λ i → inl (merid a (~ i))))
--                                     (push tt ∙ (λ i → inr (φB b i)))))
--         ◁ lem

-- --     h (inl x) = (λ i → inl (merid a₀ (~ i))) ∙ push tt
-- --     h (inr x) = sym (push tt)
-- --     h (push (a , b) i) j = help j i
-- --       where
-- --       lem : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
-- --                                 (((λ i → inl (merid a₀ (~ i))) ∙ push tt) i)
-- --                                 (push tt (~ i)))
-- --                   ((λ i₁ → inl (merid a (~ i₁))) ∙ push tt ∙ (λ i → inr (φB b i)))
-- --                   ((λ i → inr (φB b (~ i))) ∙∙ sym (push tt) ∙∙ (λ i → inl (φA a (~ i))))
-- --       lem i j =
-- --         hcomp (λ k → λ { (i = i0) → ((λ i₁ → inl ((compPath-filler (merid a) (sym (merid a₀))  (~ k)) (~ i₁))) ∙ push tt ∙ (λ i → inr (φB b i))) j
-- --                         ; (i = i1) → ((λ i → inr (φB b (~ i))) ∙∙ sym (push tt) ∙∙ (λ i → inl (φA a (~ i)))) j
-- --                         ; (j = i0) → compPath-filler'
-- --                                        (λ i → inl (merid a₀ (~ i)))
-- --                                        (push tt) k i
-- --                         ; (j = i1) → push tt (~ i)})
-- --               {!!}

-- --       help : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
-- --                                 (((λ i → inl (merid a₀ (~ i))) ∙ push tt) i)
-- --                                 (push tt (~ i)))
-- --                    (cong A0□→A∨B (cong (f1□ whitehead3x3) (push (a , b))))
-- --                    (cong W-AB (cong (fun 2ndRow≡join) (push (a , b))))
-- --       help = (cong-∙∙ A0□→A∨B (λ i → inl (merid a (~ i))) (push b) refl
-- --            ∙∙ (λ i → (λ i₁ → inl (merid a (~ i₁)))
-- --                    ∙∙ ((push tt ∙ λ i → inr (φB b i)))
-- --                    ∙∙ refl)
-- --            ∙∙ sym (compPath≡compPath' (λ i₁ → inl (merid a (~ i₁)))
-- --                                       (push tt ∙ λ i → inr (φB b i))))
-- --            ◁ (lem
-- --            ▷ sym ((λ i → sym ((λ i → inl (φA a i))
-- --                        ∙∙ push tt
-- --                        ∙∙ λ i → inr (φB b i)))))
-- -- {-
-- -- PathP
-- --       (λ i₁ →
-- --          hcomp (doubleComp-faces (λ _ → inl south) (push tt) i₁)
-- --          (inl (merid a₀ (~ i₁)))
-- --          ≡ push tt (~ i₁))
-- --       ((λ i₁ → inl (merid a (~ i₁))) ∙ push tt ∙ (λ i₁ → inr (φB b i₁)))
-- --       (λ i₁ →
-- --          (sym (λ i₂ → inl (φA a i₂)) ∙∙ sym (push tt) ∙∙ sym (λ i₂ → inr (φB b i₂)))
-- --          i₁)
-- -- -}

-- --   3x3Iso-inst : Iso (A□○ whitehead3x3) (A○□ whitehead3x3)
-- --   3x3Iso-inst = 3x3-Iso whitehead3x3

-- -- -- mainPush : Pushout (λ _ → tt) (W {A = A} {B = B})
-- -- --          → Susp (typ A) × Susp (typ B)
-- -- -- mainPush (inl x) = north , north
-- -- -- mainPush (inr x) = ⋁-fun x
-- -- -- mainPush {A = A} {B = B} (push a i) = help a i
-- -- --   where
-- -- --   thePP : (a : typ A) (b : typ B)
-- -- --     → PathP (λ i₁ → (north , north) ≡ ⋁-fun (W {A = A} {B = B} (push a b i₁)))
-- -- --       (λ i₁ → φ A a (~ i₁) , north) (λ i → north , φ B b i)
-- -- --   thePP a b i j =
-- -- --     ⋁-fun (doubleCompPath-filler
-- -- --             (λ i → inl (φ A a i))
-- -- --             (push tt)
-- -- --              (λ i → inr (φ B b i)) j i)
-- -- --   help : (a : join (typ A) (typ B))
-- -- --       → (north , north) ≡ ⋁-fun (W {A = A} {B = B} a)
-- -- --   help =
-- -- --     join-elim
-- -- --       (λ a i → φ A a (~ i) , north)
-- -- --       (λ b i → north , φ B b i)
-- -- --       thePP

-- -- -- ×→join : {!!}
-- -- -- ×→join = {!!}

-- -- -- ×→pushout : Susp (typ A) × Susp (typ B)
-- -- --           → Pushout (λ _ → tt) (W {A = A} {B = B})
-- -- -- ×→pushout {A = A} {B = B} (north , y) = inr (inr y)
-- -- -- ×→pushout {A = A} {B = B} (south , y) = inr (inr y)
-- -- -- ×→pushout {A = A} {B = B} (merid a i , north) = ({!merid a!} ∙∙ {!!} ∙∙ {!!}) i
-- -- -- ×→pushout {A = A} {B = B} (merid a i , south) = {!!}
-- -- -- ×→pushout {A = A} {B = B} (merid a i , merid a₁ i₁) = {!!}

-- -- -- PushoutIso : {!!}
-- -- -- PushoutIso = {!!}

-- -- -- WH : (n m : ℕ) → S₊ (suc (n + m)) → S₊∙ (suc n) ⋁ S₊∙ (suc m)
-- -- -- WH zero m p = inr p
-- -- -- WH (suc n) zero p = inl (subst (λ x → S₊ (2 + x)) (+-comm n zero) p)
-- -- -- WH (suc n) (suc m) p = {!WH n (suc m) ?!}
