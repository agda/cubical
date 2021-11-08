{-# OPTIONS --safe #-}
module Cubical.Homotopy.Whitehead2 where

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
  f10 whitehead3x3 = λ _ → south
  f12 whitehead3x3 = snd
  f14 whitehead3x3 = λ _ → tt
  f30 whitehead3x3 = idfun B
  f32 whitehead3x3 = snd
  f34 whitehead3x3 = λ _ → tt
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
  A0□→A∨B (push a i) = (push tt ∙ λ i → inr (φB a (~ i))) i

  A∨B→A0□ : A∨B → A0□ whitehead3x3
  A∨B→A0□ (inl x) = inl x
  A∨B→A0□ (inr north) = inl north
  A∨B→A0□ (inr south) = inl north
  A∨B→A0□ (inr (merid b i)) = (push b₀ ∙ sym (push b)) i
  A∨B→A0□ (push a i) = inl north

  firstRow≡Susp⋁ : Iso (A0□ whitehead3x3) A∨B
  fun firstRow≡Susp⋁ = A0□→A∨B
  inv firstRow≡Susp⋁ = A∨B→A0□
  rightInv firstRow≡Susp⋁ (inl x) = refl
  rightInv firstRow≡Susp⋁ (inr north) = push tt
  rightInv firstRow≡Susp⋁ (inr south) = push tt ∙ λ i → inr (merid b₀ i)
  rightInv firstRow≡Susp⋁ (inr (merid a i)) j = h j i
    where
    h : PathP (λ i → push tt i ≡ (push tt ∙ (λ i → inr (merid b₀ i))) i)
              (cong A0□→A∨B (cong A∨B→A0□ λ i → inr (merid a i)))
              (λ i → inr (merid a i))
    h = (cong-∙ A0□→A∨B (push b₀) (sym (push a))
      ∙ cong₂ _∙_ (cong (push tt ∙_)
                  (λ j i → inr (rCancel (merid b₀) j (~ i))) ∙ sym (rUnit (push tt)))
                  (symDistr (push tt) (λ i → inr (φB a (~ i)))))
      ◁ λ i j → hcomp (λ k → λ { (i = i0) → compPath-filler' (push tt)
                                                (compPath-filler (λ i → inr (φB a i)) (sym (push tt)) k) k j
                                 ; (i = i1) → inr (merid a j)
                                 ; (j = i0) → push tt (i ∨ ~ k)
                                 ; (j = i1) → compPath-filler' (push tt) (λ i → inr (merid b₀ i)) k i})
                       (inr (compPath-filler (merid a) (sym (merid b₀)) (~ i) j))

  rightInv firstRow≡Susp⋁ (push a i) j = push tt (i ∧ j)
  leftInv firstRow≡Susp⋁ (inl x) = refl
  leftInv firstRow≡Susp⋁ (inr tt) = push b₀
  leftInv firstRow≡Susp⋁ (push b i) j = help j i
    where
    help : PathP (λ i → inl north ≡ push b₀ i)
                 (cong A∨B→A0□ (cong A0□→A∨B (push b)))
                 (push b)
    help = (cong-∙ A∨B→A0□ (push tt) (λ i → inr (φB b (~ i)))
         ∙ (λ i → lUnit (sym (cong-∙ (A∨B→A0□ ∘ inr) (merid b) (sym (merid b₀)) i)) (~ i))
         ∙ cong sym (cong ((push b₀ ∙ sym (push b)) ∙_) (cong sym (rCancel (push b₀))))
         ∙ cong sym (sym (rUnit (push b₀ ∙ sym (push b)))))
         ◁ λ i j → compPath-filler' (push b₀) (sym (push b)) (~ i) (~ j)

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
      (funExt h)
      λ _ _ → tt
    where
    h : (x : A2□ whitehead3x3)
      → A0□→A∨B (f1□ whitehead3x3 x) ≡ W-AB (fun 2ndRow≡join x)
    h (inl x) = (λ i → inl (merid a₀ (~ i)))
    h (inr x) = refl
    h (push (a , b) i) j = help j i
      where
      help : PathP (λ i → Path (Pushout (λ _ → north) (λ _ → north))
                                ((inl (merid a₀ (~ i))))
                                (inr north))
                   (cong A0□→A∨B (cong (f1□ whitehead3x3) (push (a , b))))
                   (cong W-AB (cong (fun 2ndRow≡join) (push (a , b))))
      help = (cong-∙∙ A0□→A∨B (λ i → inl (merid a (~ i))) (push b) refl
            ∙ λ j → (λ i₂ → inl (merid a (~ i₂)))
                   ∙∙ compPath-filler (push tt) (λ i → inr (φB b (~ i))) (~ j)
                   ∙∙ λ i → inr (φB b (~ i ∧ j)))
           ◁ ((λ j → (λ i → inl (sym (compPath-filler (merid a) (sym (merid a₀)) j) i)) ∙∙ push tt ∙∙ λ i → inr (φB b (~ i)))
           ▷ (λ _ → (λ i → inl (φA a (~ i))) ∙∙ push tt ∙∙ λ i → inr (φB b (~ i))))

  combineIso : Iso (Susp A × Susp B) (Pushout W-AB λ _ → tt)
  combineIso = compIso (invIso PushoutColumn)
                       (compIso (3x3-Iso whitehead3x3) PushoutRows₁)

  -Susp : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
  -Susp north = south
  -Susp south = north
  -Susp (merid a i) = merid a (~ i)

  -Susp² : ∀ {ℓ} {A : Type ℓ} (x : Susp A) → -Susp (-Susp x) ≡ x
  -Susp² north = refl
  -Susp² south = refl
  -Susp² (merid a i) = refl

  -SuspIso : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (Susp A)
  fun -SuspIso = -Susp
  inv -SuspIso = -Susp
  rightInv -SuspIso = -Susp²
  leftInv -SuspIso = -Susp²

  correctIso : Iso (Susp A × Susp B) (Pushout W-AB λ _ → tt)
  correctIso = compIso (Σ-cong-iso-snd (λ _ → -SuspIso)) combineIso

  correctIsoId : Path (A∨B → Susp A × Susp B)
                      (Iso.inv correctIso ∘ inl)
                      ⋁-fun
  correctIsoId =
    funExt λ { (inl x) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr north) → ΣPathP (refl , (sym (merid b₀)))
             ; (inr south) → refl
             ; (inr (merid a i)) j → help a j i
             ; (push a i) j → north , (merid b₀ (~ j))}
    where
    lem2 : (b : B) → cong ((λ x → fun PushoutPushout
                       (fun PushoutColumn₁ (backward-l whitehead3x3
                         x)))) (push b)
                         ≡ (λ i → north , φB b i)
    lem2 b = (λ _ → cong (λ x → fun PushoutPushout
                       (fun PushoutColumn₁ x)) (push (inl b)))
          ∙∙ cong (cong (fun PushoutPushout)) (sym (rUnit (push (north , b)))) 
          ∙∙ refl

    help : (a : B) → PathP (λ i → (north , merid b₀ (~ i)) ≡ (north , south))
                 ((cong (λ x → fun (Σ-cong-iso-snd (λ _ → -SuspIso)) (fun PushoutPushout
                       (fun PushoutColumn₁ (backward-l whitehead3x3
                         (A∨B→A0□ (inr x)))))) (merid a)))
                 λ i → north , merid a i
    help a = cong (cong (fun (Σ-cong-iso-snd (λ _ → -SuspIso))))
                  ((cong-∙ ((λ x → fun PushoutPushout
                       (fun PushoutColumn₁ (backward-l whitehead3x3
                         x)))) (push b₀) (sym (push a))
        ∙∙ cong₂ _∙_ (lem2 b₀ ∙ (λ j i → north , rCancel (merid b₀) j i))
                     (cong sym (lem2 a))
        ∙∙ sym (lUnit (λ i₁ → north , φB a (~ i₁)))))
        ∙ (λ j i → north , cong-∙ -Susp (merid a) (sym (merid b₀)) j (~ i) )
         ◁ λ i j → north , compPath-filler (sym (merid a)) (merid b₀) (~ i) (~ j)

[_∣_]' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
fst ([_∣_]' {X = X} {n = n} {m = m} f g) x =
  help {X = X} f g {!!}
  where
  help : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {X : Pointed ℓ''}
       → A →∙ X
       → B →∙ X
       → (A ⋁ B → typ X)
  help f g (inl x) = fst f x
  help f g (inr x) = fst g x
  help f g (push a i) = (snd f ∙ sym (snd g)) i
snd ([_∣_]' {n = n} {m = m} f g) = {!joinIso!}
