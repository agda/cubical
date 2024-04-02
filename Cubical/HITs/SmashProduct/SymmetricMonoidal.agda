{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.SymmetricMonoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.SmashProduct.Base
open import Cubical.HITs.SmashProduct.Pentagon
open import Cubical.HITs.SmashProduct.Hexagon

private
  variable
    ℓ ℓ' : Level
    A B : Pointed ℓ

⋀→∙-idfun : {A : Pointed ℓ} {B : Pointed ℓ'}
  → (_⋀→∙_ (idfun∙ A) (idfun∙ B)) ≡ idfun∙ (A ⋀∙ B)
⋀→∙-idfun =
  ΣPathP (funExt
    (⋀-fun≡ _ _ refl (λ _ → refl)
      (λ x → flipSquare (sym (rUnit (push (inl x)))))
      λ x → flipSquare (sym (rUnit (push (inr x)))))
                   , refl)

⋀→∙-comp : {A A' A'' B B' B'' : Pointed ℓ}
  (f : A →∙ A') (f' : A' →∙ A'')
  (g : B →∙ B') (g' : B' →∙ B'')
  → ((f' ∘∙ f) ⋀→∙ (g' ∘∙ g)) ≡ ((f' ⋀→∙ g') ∘∙ (f ⋀→∙ g))
⋀→∙-comp f f' g g' =
  ΣPathP ((funExt
   (⋀-fun≡ _ _ refl (λ _ → refl)
     (λ x → flipSquare
       (cong (push (inl (fst f' (fst f x))) ∙_)
         ((λ i j → cong-∙ (λ y → inr (fst f' (fst f x) , y))
                        (cong (fst g') (snd g)) (snd g') i (~ j))
        ∙ symDistr (cong (λ y → inr (fst f' (fst f x) , y))
                          (λ i → fst g' (snd g i)))
                    (cong (λ y → inr (fst f' (fst f x) , y)) (snd g')))
       ∙ assoc _ _ _
       ∙∙ (λ j → (push (inl (fst f' (fst f x)))
           ∙ (λ j → inr (fst f' (fst f x) , snd g' (~ j))))
           ∙ λ j → inr (fst f' (f .fst x) , fst g' (snd g (~ j))))
       ∙∙ sym (cong-∙ (f' ⋀→ g') (push (inl (fst f x)))
         λ i → inr (fst f x , g .snd (~ i)))))
     λ x → flipSquare
       (cong (push (inr (fst g' (fst g x))) ∙_)
         ((λ i j → cong-∙ (λ y → inr (y , fst g' (fst g x)))
                        (cong (fst f') (snd f)) (snd f') i (~ j))
        ∙ symDistr (cong (λ y → inr (y , fst g' (fst g x)))
                          (λ i → fst f' (snd f i)))
                    (cong (λ y → inr (y , fst g' (fst g x))) (snd f')))
       ∙ assoc _ _ _
       ∙∙ (λ j → (push (inr (fst g' (fst g x)))
           ∙ (λ j → inr (snd f' (~ j) , fst g' (fst g x))))
           ∙ λ j → inr (fst f' (snd f (~ j)) , fst g' (g .fst x)))
       ∙∙ sym (cong-∙ (f' ⋀→ g') (push (inr (fst g x)))
                  λ i → inr ((snd f (~ i)) , fst g x)))))
        , (rUnit refl))

⋀assoc-⋀→∙ : {A A' B B' C C' : Pointed ℓ}
  (f : A →∙ A') (g : B →∙ B') (h : C →∙ C') →
      ≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))
    ≡ ((f ⋀→∙ g) ⋀→∙ h) ∘∙ ≃∙map SmashAssocEquiv∙
⋀assoc-⋀→∙ {A = A} {A' = A'} {B = B} {B' = B'} {C = C} {C' = C'} f g h =
  ΣPathP
   ((funExt (⋀-fun≡'.main _ _
     (λ x → mainᵣ (fst x) (snd x))
     (λ x → p≡refl ◁ flipSquare
       (cong (cong (SmashAssocIso .Iso.fun))
         (sym (rUnit (push (inl (fst f x))))))
         ▷ λ _ → refl)
     (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
       λ y z → (λ i → push-lem y z (~ i)
                    ∙∙ refl
                    ∙∙ sym (push-lem y z i0))
           ∙ ∙∙lCancel (sym (push-lem y z i0))
           ∙ sym p≡refl)))
  , λ i j → pt-lem-main i j)
  where
  mainᵣ : (x : fst A) (y : B ⋀ C)
    → SmashAssocIso .Iso.fun (inr (fst f x , (g ⋀→ h) y))
     ≡ ((f ⋀→∙ g) ⋀→ h) (SmashAssocIso .Iso.fun (inr (x , y)))
  mainᵣ x =
    ⋀-fun≡ _ _ refl (λ _ → refl)
      (λ b → flipSquare
        (cong-∙ (λ z → SmashAssocIso .Iso.fun (inr (fst f x , z)))
                (push (inl (fst g b)))
                (λ i₁ → inr (fst g b , snd h (~ i₁)))))
      λ b → flipSquare
        (cong-∙ (λ z → SmashAssocIso .Iso.fun (inr (fst f x , z)))
                (push (inr (fst h b)))
                (λ i₁ → inr (snd g (~ i₁) , fst h b))
       ∙∙ cong₂ _∙_ ((λ j i → ⋀CommIso .Iso.fun
                   (compPath≡compPath'
                     (push (inl (fst h b)))
                     (λ i → inr (fst h b , push (inl (fst f x)) i)) (~ j) i))
                    ∙ cong-∙ (⋀CommIso .Iso.fun)
                        (push (inl (fst h b)))
                        λ i → inr (fst h b , push (inl (fst f x)) i))
                    refl
        ∙ sym (assoc _ _ _)
        ∙ cong₂ _∙_ refl (sym (cong-∙ (λ y → (inr (y , fst h b)))
                                (push (inl (fst f x)))
                                (λ i₁ → inr (fst f x , snd g (~ i₁)))))
       ∙∙ sym (lem b))
     where
     lem : (b : _) → cong ((f ⋀→∙ g) ⋀→ h)
             (cong (SmashAssocIso .Iso.fun) λ i → inr (x , push (inr b) i))
          ≡ (push (inr (fst h b)))
          ∙ λ i → inr (((push (inl (fst f x))
          ∙ λ i₁ → inr (fst f x , snd g (~ i₁))) i) , (fst h b))
     lem b = (λ j i → ((f ⋀→∙ g) ⋀→ h)
                 (⋀CommIso .Iso.fun
                   (compPath≡compPath' (push (inl b))
                     (λ i → inr (b , push (inl x) i)) (~ j) i)))
           ∙∙ cong-∙ (((f ⋀→∙ g) ⋀→ h) ∘ ⋀CommIso .Iso.fun)
                (push (inl b)) (λ i → inr (b , push (inl x) i))
           ∙∙ cong₂ _∙_
               (sym (rUnit _))
               refl

  push-lem : (y : _) (z : _)
    → cong (((f ⋀→∙ g) ⋀→ h) ∘ (fst (fst SmashAssocEquiv∙)))
            (push (inr (inr (y , z))))
     ≡ cong (fst (≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))))
            (push (inr (inr (y , z))))
  push-lem y z =
      cong (cong ((f ⋀→∙ g) ⋀→ h))
           (cong-∙∙ ⋀comm→ (push (inl z))
                            (λ i → inr (z , push (inr y) i))
                            refl
         ∙ sym (compPath≡compPath' (push (inr z)) _))
   ∙∙ cong-∙ ((f ⋀→∙ g) ⋀→ h)
        (push (inr z)) (λ i → inr (push (inr y) i , z))
   ∙∙ (cong₂ _∙_ (sym (rUnit (push (inr (fst h z)))))
                 (cong-∙ (λ x → inr (x , fst h z))
                         (push (inr (fst g y)))
                         (λ i → inr (snd f (~ i) , fst g y)))
     ∙ sym (cong-∙ (SmashAssocIso .Iso.fun)
             (push (inr (inr (fst g y , fst h z))))
             (λ i → inr (snd f (~ i)
                        , inr (fst g y , fst h z)))
        ∙∙ cong (_∙ (λ i → inr (inr (snd f (~ i) , fst g y) , fst h z)))
                (cong-∙∙ ⋀comm→
                         (push (inl (fst h z)))
                         (λ i → inr (fst h z , push (inr (fst g y)) i))
                         refl
             ∙ sym (compPath≡compPath' (push (inr (fst h z))) _))
        ∙∙ sym (assoc _ _ _)))

  module N = ⋀-fun≡'
      (λ z → SmashAssocIso .Iso.fun ((f ⋀→ (g ⋀→∙ h)) z))
      (λ z → ((f ⋀→∙ g) ⋀→ h) (SmashAssocIso .Iso.fun z))
      (λ x₁ → mainᵣ (fst x₁) (snd x₁))

  p≡refl : N.p ≡ refl
  p≡refl = (λ j → cong (SmashAssocIso .Iso.fun
                       ∘ ((f ⋀→ (g ⋀→∙ h))))
                         (push (inr (inl tt)))
                 ∙∙ refl
                 ∙∙ cong (((f ⋀→∙ g) ⋀→ h)
                         ∘ (SmashAssocIso .Iso.fun))
                         (sym (push (push tt j))))
          ∙ cong (λ x → x ∙∙ refl ∙∙ refl)
                  (cong-∙ (SmashAssocIso .Iso.fun)
                          (push (inr (inl tt)))
                          (λ i → inr (snd f (~ i) , inl tt))
                 ∙ sym (rUnit refl))
          ∙ sym (rUnit refl)

  pt-lem : cong (fst (≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))))
             (push (inr (inl tt)))
         ≡ cong (fst (((f ⋀→∙ g) ⋀→∙ h) ∘∙ ≃∙map SmashAssocEquiv∙))
             (push (inr (inl tt)))
  pt-lem i j =
    fst (≃∙map SmashAssocEquiv∙) (rUnit (push (inr (inl tt))) (~ i) j)

  pt-lem-main : I → I → _
  pt-lem-main i j =
    hcomp (λ k → λ {(i = i0) → rUnit (refl {x = inl tt}) k j
                   ; (i = i1) → rUnit (refl {x = inl tt}) k j
                   ; (j = i0) → (pt-lem i0 ∙∙ refl ∙∙ sym (pt-lem k)) i
                   ; (j = i1) → inl tt})
          (∙∙lCancel (sym (pt-lem i0)) j i)

⋀comm-sq : {A A' B B' : Pointed ℓ}
  (f : A →∙ A') (g : B →∙ B')
  → (⋀comm→∙ ∘∙ (f ⋀→∙ g)) ≡ ((g ⋀→∙ f) ∘∙ ⋀comm→∙)
⋀comm-sq f g =
  ΣPathP ((funExt
    (⋀-fun≡ _ _ refl (λ _ → refl)
      (λ x → flipSquare
        (cong-∙ ⋀comm→
          (push (inl (fst f x))) (λ i → inr (fst f x , snd g (~ i)))))
      λ b → flipSquare (cong-∙ ⋀comm→
                         (push (inr (fst g b)))
                         (λ i → inr (snd f (~ i) , fst g b)))))
    , refl)

⋀comm-sq' : {A A' B B' : Pointed ℓ}
  (f : A →∙ A') (g : B →∙ B')
  → (f ⋀→∙ g) ≡ (⋀comm→∙ ∘∙ ((g ⋀→∙ f) ∘∙ ⋀comm→∙))
⋀comm-sq' f g =
     sym (∘∙-idʳ (f ⋀→∙ g))
  ∙∙ cong (_∘∙ (f ⋀→∙ g)) (sym lem)
  ∙∙ ∘∙-assoc ⋀comm→∙ ⋀comm→∙ (f ⋀→∙ g)
   ∙ cong (λ w → ⋀comm→∙ ∘∙ w) (⋀comm-sq f g)
  where
  lem : ⋀comm→∙ ∘∙ ⋀comm→∙ ≡ idfun∙ _
  lem = ΣPathP ((funExt (Iso.rightInv ⋀CommIso)) , (sym (rUnit refl)))

Bool⋀→ : Bool*∙ {ℓ} ⋀ A → typ A
Bool⋀→ {A = A} (inl x) = pt A
Bool⋀→ (inr (lift false , a)) = a
Bool⋀→ {A = A} (inr (lift true , a)) = pt A
Bool⋀→ {A = A} (push (inl (lift false)) i) = pt A
Bool⋀→ {A = A} (push (inl (lift true)) i) = pt A
Bool⋀→ {A = A} (push (inr x) i) = pt A
Bool⋀→ {A = A} (push (push a i₁) i) = pt A

⋀lIdIso : Iso (Bool*∙ {ℓ} ⋀ A) (typ A)
Iso.fun (⋀lIdIso {A = A}) (inl x) = pt A
Iso.fun ⋀lIdIso = Bool⋀→
Iso.inv ⋀lIdIso a = inr (false* , a)
Iso.rightInv ⋀lIdIso a = refl
Iso.leftInv (⋀lIdIso {A = A}) =
  ⋀-fun≡ _ _ (sym (push (inl false*))) h hₗ
    λ x → compPath-filler (sym (push (inl false*))) (push (inr x))
  where
  h : (x : (Lift Bool) × fst A) →
      inr (false* , Bool⋀→ (inr x)) ≡ inr x
  h (lift false , a) = refl
  h (lift true , a) = sym (push (inl false*)) ∙ push (inr a)

  hₗ : (x : Lift Bool) →
      PathP
      (λ i → inr (false* , Bool⋀→ (push (inl x) i)) ≡ push (inl x) i)
      (λ i → push (inl false*) (~ i)) (h (x , pt A))
  hₗ (lift false) i j = push (inl false*) (~ j ∨ i)
  hₗ (lift true) =
      compPath-filler (sym (push (inl false*))) (push (inl true*))
    ▷ (cong (sym (push (inl false*)) ∙_)
       λ j i → push (push tt j) i)

⋀lIdEquiv∙ : Bool*∙ {ℓ} ⋀∙ A ≃∙ A
fst ⋀lIdEquiv∙ = isoToEquiv ⋀lIdIso
snd ⋀lIdEquiv∙ = refl

⋀lId-sq : (f : A →∙ B) →
      (≃∙map (⋀lIdEquiv∙ {ℓ}) ∘∙ (idfun∙ Bool*∙ ⋀→∙ f))
    ≡ (f ∘∙ ≃∙map ⋀lIdEquiv∙)
⋀lId-sq {ℓ} {A = A} {B = B} f =
  ΣPathP ((funExt
    (⋀-fun≡ _ _ (sym (snd f)) (λ x → h (fst x) (snd x)) hₗ hᵣ))
  , (sym (rUnit refl) ◁ (λ i j → snd f (~ i ∨ j))
    ▷ lUnit (snd f)))
  where
  h : (x : Lift Bool) (a : fst A)
    → Bool⋀→ (inr (x , fst f a)) ≡ fst f (Bool⋀→ (inr (x , a)))
  h (lift false) a = refl
  h (lift true) a = sym (snd f)

  hₗ : (x : Lift Bool)
    → PathP (λ i → Bool⋀→ ((idfun∙ Bool*∙ ⋀→ f) (push (inl x) i))
                   ≡ fst f (Bool⋀→ (push (inl x) i)))
             (sym (snd f)) (h x (pt A))
  hₗ (lift false) =
    flipSquare ((cong-∙ (Bool⋀→ {ℓ})
                  (push (inl false*))
                  (λ i → inr (lift false , snd f (~ i)))
              ∙ sym (lUnit (sym (snd f))))
             ◁ λ i j → snd f (~ i ∧ ~ j))
  hₗ (lift true) =
    flipSquare
       ((cong-∙ (Bool⋀→ {ℓ})
         (push (inl true*)) (λ i → inr (lift true , snd f (~ i)))
       ∙ sym (rUnit refl))
      ◁ λ i _ → snd f (~ i))

  hᵣ : (x : fst A)
    → PathP (λ i → Bool⋀→ {ℓ} ((idfun∙ Bool*∙ ⋀→ f) (push (inr x) i))
                   ≡ fst f (snd A))
             (sym (snd f)) (h true* x)
  hᵣ x = flipSquare ((cong-∙ (Bool⋀→ {ℓ})
                      (push (inr (fst f x)))
                      (λ i → inr (true* , fst f x))
                    ∙ sym (rUnit refl))
      ◁ λ i _ → snd f (~ i))

⋀lId-assoc : ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ⋀→∙ idfun∙ B)
             ∘∙ ≃∙map SmashAssocEquiv∙)
            ≡ ≃∙map ⋀lIdEquiv∙
⋀lId-assoc {ℓ} {A = A} {B = B} =
  ΣPathP (funExt
          (⋀-fun≡'.main _ _
            (λ xy → mainᵣ (fst xy) (snd xy))
            (λ x → sym (rUnit refl) ◁ mainᵣ-pt-coh x)
            (⋀→∙Homogeneous≡ (isHomogeneousPath _ _) mainᵣ-coh))
        , (sym (rUnit refl)
          ◁ flipSquare (sym (rUnit refl))))
  where
  l₁ : (x : Lift Bool) → inl tt ≡ Bool⋀→ (inr (x , inl tt))
  l₁ (lift true) = refl
  l₁ (lift false) = refl

  l₂ : (x : Lift Bool) (y : fst A × fst B)
    → inr (Bool⋀→ (inr (x , fst y)) , snd y)
    ≡ Bool⋀→ (inr (x , inr y))
  l₂ (lift true) y = sym (push (inr (snd y)))
  l₂ (lift false) y = refl

  l₁≡l₂-left : (x : Lift Bool) (y : fst A) →
    PathP (λ i → l₁ x i ≡ l₂ x (y , pt B) i)
          (push (inl (Bool⋀→ (inr (x , y)))))
          λ i → Bool⋀→ {ℓ} {A = A ⋀∙ B} (inr (x , push (inl y) i))
  l₁≡l₂-left (lift true) y = (λ i → push (push tt i))
                   ◁ λ i j → push (inr (pt B)) (~ i ∧ j)
  l₁≡l₂-left (lift false) y = refl

  l₁≡l₂-right : (x : Lift Bool) (y : fst B)
    → PathP (λ i → l₁ x i ≡ l₂ x ((pt A) , y) i)
            (push (inr y) ∙ (λ i → inr (Bool⋀→ {A = A} (push (inl x) i) , y)))
            (λ i → Bool⋀→ {A = A ⋀∙ B} (inr (x , push (inr y) i)))
  l₁≡l₂-right (lift false) y = sym (rUnit (push (inr y)))
  l₁≡l₂-right (lift true) y = sym (rUnit (push (inr y)))
                   ◁ λ i j → push (inr y) (j ∧ ~ i)

  mainᵣ : (x : Lift Bool) (y : A ⋀ B)
    → (≃∙map ⋀lIdEquiv∙ ⋀→ idfun∙ B)
        (SmashAssocIso .Iso.fun (inr (x , y)))
     ≡ Bool⋀→ {ℓ} (inr (x , y))
  mainᵣ x = ⋀-fun≡ _ _ (l₁ x) (l₂ x)
    (λ y → flipSquare (sym (rUnit (push (inl (Bool⋀→ (inr (x , y))))))
          ◁ l₁≡l₂-left x y))
    λ y → flipSquare (
      (cong (cong (≃∙map ⋀lIdEquiv∙ ⋀→ idfun∙ B))
            (cong-∙∙ ⋀comm→
              (push (inl y)) (λ i → inr (y , push (inl x) i)) refl
          ∙ sym (compPath≡compPath'
                  (push (inr y)) (λ i → inr (push (inl x) i , y))))
        ∙ cong-∙ (≃∙map ⋀lIdEquiv∙ ⋀→ idfun∙ B)
            (push (inr y)) λ i → inr (push (inl x) i , y))
        ◁ (cong₂ _∙_ (sym (rUnit (push (inr y))))
                     refl
                   ◁ l₁≡l₂-right x y))

  mainᵣ-pt-coh : (x : Lift Bool)
    → PathP (λ i → inl tt ≡ Bool⋀→ (push (inl x) i))
             refl (mainᵣ x (inl tt))
  mainᵣ-pt-coh (lift false) = refl
  mainᵣ-pt-coh (lift true) = refl

  module N = ⋀-fun≡'
    (λ z → (≃∙map ⋀lIdEquiv∙ ⋀→ idfun∙ B) (SmashAssocIso .Iso.fun z))
    (λ z → ⋀lIdIso .Iso.fun z)
    (λ xy → mainᵣ (fst xy) (snd xy))
  open N

  lem : (x : fst A) (y : fst B)
    → cong ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ⋀→ idfun∙ B)
            ∘ SmashAssocIso .Iso.fun)
             (push (inr (inr (x , y))))
    ≡ push (inr y)
  lem x y =
      cong (cong (≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ⋀→ idfun∙ B))
            (cong-∙∙ ⋀comm→
              (push (inl y)) (λ i → inr (y , push (inr x) i)) refl
           ∙ sym (compPath≡compPath'
                  (push (inr y)) λ i → inr (push (inr x) i , y)))
    ∙∙ cong-∙ (≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ⋀→ idfun∙ B)
              (push (inr y))
              (λ i → inr (push (inr x) i , y))
    ∙∙ (sym (rUnit _)
     ∙ sym (rUnit _))

  mainᵣ-coh : (x : fst A) (y : fst B)
    → Fₗ .fst (inr (x , y)) ≡ Fᵣ .fst (inr (x , y))
  mainᵣ-coh x y =
      (λ i → lem x y i ∙∙ sym (lem x y i1) ∙∙ refl)
    ∙ sym (compPath≡compPath'
           (push (inr y)) (sym (push (inr y))))
    ∙ rCancel (push (inr y))
    ∙ rUnit refl

-- Triangle equality
⋀triang : ∀ {ℓ} {A B : Pointed ℓ}
  → (((≃∙map (⋀lIdEquiv∙ {ℓ}) ∘∙ ⋀comm→∙) ⋀→∙ idfun∙ B)
    ∘∙ ≃∙map SmashAssocEquiv∙)
    ≡ idfun∙ A ⋀→∙ ≃∙map (⋀lIdEquiv∙ {ℓ} {A = B})
⋀triang {ℓ = ℓ} {A = A} {B = B} =
  ΣPathP ((funExt (⋀-fun≡'.main _ _
    (λ x → mainᵣ (fst x) (snd x))
    (λ x → p≡refl
         ◁ flipSquare ((λ i j → push (inl x) (i ∧ j))
         ▷ rUnit (push (inl x))))
    (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
      λ x y → Fₗ≡refl x y ∙ sym (Fᵣ≡refl x y))))
    , (sym (rUnit refl) ◁ flipSquare p≡refl))
  where
  mainᵣ-hom : (x : fst A) (y : Bool* {ℓ}) (z : fst B)
    → Path (A ⋀ B) (inr (Bool⋀→ (inr (y , x)) , z))
                    (inr (x , Bool⋀→ (inr (y , z))))
  mainᵣ-hom x (lift false) z = refl
  mainᵣ-hom x (lift true) z = sym (push (inr z)) ∙ push (inl x)

  mainᵣ : (x : fst A) (y : Bool*∙ {ℓ} ⋀ B) →
    ((≃∙map (⋀lIdEquiv∙ {ℓ}) ∘∙ ⋀comm→∙) ⋀→ (idfun∙ B))
      (Iso.fun (SmashAssocIso {A = A} {B = Bool*∙ {ℓ}} {C = B}) (inr (x , y)))
    ≡ inr (x , ⋀lIdIso .Iso.fun y)
  mainᵣ x = ⋀-fun≡ _ _ (push (inl x))
    (λ y → mainᵣ-hom x (fst y) (snd y))
    (λ { (lift false) → flipSquare (sym (rUnit (push (inl x)))
                       ◁ λ i j → push (inl x) (j ∨ i))
       ; (lift true) → flipSquare ((sym (rUnit (push (inl (pt A))))
                                   ∙ λ j i → push (push tt j) i)
                     ◁ λ i j → compPath-filler'
                                 (sym (push (inr (pt B)))) (push (inl x)) j i)})
     λ b → flipSquare
       ((cong (cong (((≃∙map (⋀lIdEquiv∙ {ℓ}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)))
         (cong-∙∙ ⋀comm→ (push (inl b)) (λ i → inr (b , push (inl x) i)) refl
         ∙ sym (compPath≡compPath'
                 (push (inr b)) (λ i → inr (push (inl x) i , b))))
       ∙ cong-∙ (((≃∙map (⋀lIdEquiv∙ {ℓ})  ∘∙ ⋀comm→∙) ⋀→ idfun∙ B))
                (push (inr b)) (λ i → inr (push (inl x) i , b))
       ∙ sym (rUnit _)
       ∙ (λ i → (push (inr b) ∙ (λ j → inr (rUnit (λ _ → pt A) (~ i) j , b))))
       ∙ sym (rUnit (push (inr b))))
       ◁ λ i j → compPath-filler' (sym (push (inr b))) (push (inl x)) j i)

  lemₗ : cong (idfun∙ A ⋀→ ≃∙map (⋀lIdEquiv∙ {ℓ} {A = B}))
             (push (inr (inl tt)))
      ≡ (push (inl (snd A)))
  lemₗ = sym (rUnit _) ∙ λ i → push (push tt (~ i))

  module K = ⋀-fun≡' (λ z →
          ((≃∙map ⋀lIdEquiv∙ ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)
          (SmashAssocIso .Iso.fun z))
       (λ z → (idfun∙ A ⋀→ ≃∙map ⋀lIdEquiv∙) z)
       (λ x₁ → mainᵣ (fst x₁) (snd x₁))
  open K

  p≡refl : p ≡ refl
  p≡refl = cong (push (inl (snd A)) ∙_) (cong sym lemₗ)
         ∙ rCancel (push (inl (pt A)))

  Fₗ-false : (y : fst B)
    → cong ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)
        (cong ⋀comm→ (push (inl y)
                   ∙' (λ i → inr (y , push (inr (lift false)) i))))
      ≡ push (inr y)
  Fₗ-false y =
      cong (cong ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B))
         (cong (cong ⋀comm→)
           (sym (compPath≡compPath'
             (push (inl y)) (λ i → inr (y , push (inr (lift false)) i))))
       ∙ cong-∙ ⋀comm→ (push (inl y))
                        (λ i → inr (y , push (inr (lift false)) i)))
    ∙∙ cong-∙ ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)
              (push (inr y)) (λ i → inr (push (inr (lift false)) i , y))
    ∙∙ (sym (rUnit _)
     ∙ (λ i → push (inr y) ∙ (λ j → inr (rUnit (λ _ → pt A) (~ i) j , y)))
     ∙ sym (rUnit _))

  Fₗ-true : (y : fst B)
    → cong ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)
        (cong (SmashAssocIso .Iso.fun) (push (inr (inr (lift true , y)))))
      ≡ push (inr y)
  Fₗ-true y =
      cong (cong ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B))
        (cong-∙∙ ⋀comm→ (push (inl y)) (λ i → inr (y , push (inr true*) i)) refl
        ∙ sym (compPath≡compPath' (push (inr y))
                                  λ i → inr (push (inr true*) i , y)))
    ∙∙ cong-∙ ((≃∙map (⋀lIdEquiv∙ {ℓ} {A = A}) ∘∙ ⋀comm→∙) ⋀→ idfun∙ B)
              (push (inr y))
              (λ i → inr (push (inr true*) i , y))
    ∙∙ ((sym (rUnit _)
     ∙ (λ i → push (inr y) ∙ (λ j → inr (rUnit (λ _ → pt A) (~ i) j , y)))
     ∙ sym (rUnit _)))

  Fₗ≡refl : (x : Lift Bool) (y : fst B) → Fₗ .fst (inr (x , y)) ≡ refl
  Fₗ≡refl (lift false) y =
     (λ i → Fₗ-false y i ∙∙ refl ∙∙ sym (rUnit (push (inr y)) (~ i)))
    ∙ ∙∙lCancel _
  Fₗ≡refl (lift true) y =
      (λ j → Fₗ-true y j
          ∙∙ (sym (push (inr y)) ∙ push (push tt j))
          ∙∙ sym (rUnit (push (inr (pt B))) (~ j)))
    ∙ (λ j → (λ i → push (inr y) (i ∧ ~ j))
           ∙∙ (λ i → push (inr y) (~ j ∧ ~ i))
            ∙ push (inr (pt B))
           ∙∙ sym (push (inr (pt B))))
    ∙ cong (_∙ sym (push (inr (pt B)))) (sym (lUnit (push (inr (pt B)))))
    ∙ rCancel _

  Fᵣ≡refl : (x : Lift Bool) (y : fst B) → Fᵣ .fst (inr (x , y)) ≡ refl
  Fᵣ≡refl x y =
    cong (push (inl (snd A)) ∙_)
      (sym (rUnit _) ∙ (λ i j → push (push tt (~ i)) (~ j)))
    ∙ rCancel _
