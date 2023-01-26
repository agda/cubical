{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.SymmetricMonoidal where

open import Cubical.HITs.SmashProduct.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Wedge
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.HITs.SmashProduct.Base
open import Cubical.HITs.SmashProduct.Pentagon


private
  variable
    ℓ ℓ' : Level
    A B C D : Pointed ℓ

record isSymmetricMonoidal {ℓ : Level}
  (_⊗_ : Pointed ℓ → Pointed ℓ → Pointed ℓ)
  : Type (ℓ-suc ℓ) where
  field
    ⊗fun : {A B A' B' : _} (f : A →∙ A') (g : B →∙ B')
      → (A ⊗ B) →∙ (A' ⊗ B')

    ⊗fun-id : {A B : _} → ⊗fun (idfun∙ A) (idfun∙ B) ≡ idfun∙ (A ⊗ B)

    ⊗-comp : {A A' A'' B B' B'' : _}
      (f : A →∙ A') (f' : A' →∙ A'')
      (g : B →∙ B') (g' : B' →∙ B'')
      → ⊗fun (f' ∘∙ f) (g' ∘∙ g) ≡ (⊗fun f' g' ∘∙ ⊗fun f g)

    ⊗assoc : {A B C : _} → (A ⊗ (B ⊗ C)) ≃∙ ((A ⊗ B) ⊗ C)

    ⊗assoc-sq : {A A' B B' C C' : _}
         (f : A →∙ A') (g : B →∙ B') (h : C →∙ C')
      → (≃∙map (⊗assoc {A = A'} {B = B'} {C = C'})
        ∘∙ ⊗fun f (⊗fun g h))
        ≡ (⊗fun (⊗fun f g) h ∘∙ ≃∙map ⊗assoc)

    ⊗pentagon : {A B C D : _}
      → ((≃∙map ⊗assoc)
        ∘∙ ≃∙map (⊗assoc {A = A} {B = B} {C =  (C ⊗ D)}))
       ≡ (⊗fun (≃∙map ⊗assoc) (idfun∙ D)
         ∘∙ (≃∙map ⊗assoc
         ∘∙ ⊗fun (idfun∙ A) (≃∙map ⊗assoc)))

    ⊗comm : {A B : _} → (A ⊗ B) →∙ (B ⊗ A)
    ⊗comm-sq : {A A' B B' : _} (f : A →∙ A') (g : B →∙ B')
       → (⊗comm ∘∙ ⊗fun f g)
        ≡ (⊗fun g f ∘∙ ⊗comm)

    hexagon : {A B C : _}
      → (⊗fun ⊗comm (idfun∙ B)
       ∘∙ (≃∙map ⊗assoc
       ∘∙ ⊗fun (idfun∙ A) (⊗comm {A = B} {B = C})))
      ≡ (≃∙map ⊗assoc ∘∙ (⊗comm ∘∙ ≃∙map ⊗assoc))

    ⊗commid : {A B : _} → (⊗comm ∘∙ ⊗comm {A = A} {B = B}) ≡ idfun∙ (A ⊗ B)

    ⊗Unit : Pointed ℓ

    ⊗lId : {A : Pointed ℓ} → (⊗Unit ⊗ A) ≃∙ A

    ⊗lId-sq : {A B : _} (f : A →∙ B)
      → (≃∙map ⊗lId ∘∙ ⊗fun (idfun∙ ⊗Unit) f)
       ≡ (f ∘∙ ≃∙map ⊗lId)

    ⊗lId-assoc : {A B : _}
      → (⊗fun (≃∙map (⊗lId {A = A})) (idfun∙ B) ∘∙ ≃∙map ⊗assoc)
        ≡ ≃∙map ⊗lId

open isSymmetricMonoidal

⋀→∙-idfun : {A : Pointed ℓ} {B : Pointed ℓ'}
  → (_⋀→∙_ (idfun∙ A) (idfun∙ B)) ≡ idfun∙ (A ⋀∙ B)
⋀→∙-idfun =
  ΣPathP (funExt
    (⋀-fun≡ _ _ refl (λ _ → refl)
      (λ x → flipSquare (sym (rUnit (push (inl x)))))
      λ x → flipSquare (sym (rUnit (push (inr x)))))
                   , refl)

⋀→∙-comp : {A A' A'' B B' B'' : Pointed ℓ}
  (f : A →∙ A') (f' : A' →∙ A'') (g : B →∙ B')
  (g' : B' →∙ B'')
  → ((f' ∘∙ f) ⋀→∙ (g' ∘∙ g)) ≡ ((f' ⋀→∙ g') ∘∙ (f ⋀→∙ g))
⋀→∙-comp f f' g g' =
  ΣPathP ((funExt (⋀-fun≡ _ _ refl (λ _ → refl)
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

⋀assoc-sq : {A A' B B' C C' : Pointed ℓ}
  (f : A →∙ A') (g : B →∙ B') (h : C →∙ C') →
      (≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))) ≡
      (((f ⋀→∙ g) ⋀→∙ h) ∘∙ ≃∙map SmashAssocEquiv∙)
⋀assoc-sq {A = A}{A' = A'} {B = B} {B' = B'} {C = C} {C' = C'} f g h = ΣPathP
   ((funExt (⋀-fun≡'.main _ _
     (λ x → f1 (fst x) (snd x))
     (λ x → p≡refl₁ ◁ flipSquare
       (cong (cong (SmashAssocIso .Iso.fun))
         (sym (rUnit (push (inl (fst f x))))))
         ▷ λ _ → refl)
     (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
       λ y z → {!fst
      (⋀-fun≡'.Fₗ
       (λ z₁ → fst (≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))) z₁)
       (λ z₁ → fst (((f ⋀→∙ g) ⋀→∙ h) ∘∙ ≃∙map SmashAssocEquiv∙) z₁)
       (λ x → f1 (fst x) (snd x)))
      (inr (y , z))!} ∙ {!!} ∙ sym p≡refl₁)))
  , {!!})
  where
  module _ (x : fst A) where
    f₁ₗ : B ⋀∙ C →∙ ((A' ⋀∙ B') ⋀∙ C')
    fst f₁ₗ y = SmashAssocIso .Iso.fun (inr (fst f x , (g ⋀→ h) y))
    snd f₁ₗ = refl

    f₁ᵣ : B ⋀∙ C →∙ ((A' ⋀∙ B') ⋀∙ C')
    fst f₁ᵣ y = ((f ⋀→∙ g) ⋀→ h) (SmashAssocIso .Iso.fun (inr (x , y)))
    snd f₁ᵣ = refl

  f1 : (x : fst A) (y : B ⋀ C)
    → SmashAssocIso .Iso.fun (inr (fst f x , (g ⋀→ h) y))
     ≡ ((f ⋀→∙ g) ⋀→ h) (SmashAssocIso .Iso.fun (inr (x , y)))
  f1 x =
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
       ∙∙ sym (help b))
     where
     help : (b : _) → cong ((f ⋀→∙ g) ⋀→ h)
             (cong (SmashAssocIso .Iso.fun) λ i → inr (x , push (inr b) i))
          ≡ (push (inr (fst h b)))
          ∙ λ i → inr (((push (inl (fst f x))
          ∙ λ i₁ → inr (fst f x , snd g (~ i₁))) i) , (fst h b))
     help b = (λ j i → ((f ⋀→∙ g) ⋀→ h)
                 (⋀CommIso .Iso.fun
                   (compPath≡compPath' (push (inl b))
                     (λ i → inr (b , push (inl x) i)) (~ j) i)))
           ∙∙ cong-∙ (((f ⋀→∙ g) ⋀→ h) ∘ ⋀CommIso .Iso.fun)
                (push (inl b)) (λ i → inr (b , push (inl x) i))
           ∙∙ cong₂ _∙_
               (sym (rUnit _))
               refl

     help2 : (y : _) (z : _)
       → cong (((f ⋀→∙ g) ⋀→ h)
                     ∘ (fst (fst SmashAssocEquiv∙)))
                   (push (inr (inr (y , z))))
        ≡ cong (fst (≃∙map SmashAssocEquiv∙ ∘∙ (f ⋀→∙ (g ⋀→∙ h))))
                 (push (inr (inr (y , z))))
     help2 y z = cong (cong ((f ⋀→∙ g) ⋀→ h))
                   (cong (cong (⋀CommIso .Iso.fun))
                     (compPath≡compPath'
                       {!!} {!!})
                  ∙ {!!})
              ∙∙ {!!}
              ∙∙ {!cong (((fst (fst SmashAssocEquiv∙))))
                   (push (inr (inr (y , z))))!}
{-
cong f (push (inr b)) ∙∙ pr (pt A , b) ∙∙ sym (cong g (push (inr b)))
-}

  module N = ⋀-fun≡' (λ z → SmashAssocIso .Iso.fun ((f ⋀→ (g ⋀→∙ h)) z))
      (λ z → ((f ⋀→∙ g) ⋀→ h) (SmashAssocIso .Iso.fun z))
      (λ x₁ → f1 (fst x₁) (snd x₁))

  p≡refl₁ : N.p ≡ refl
  p≡refl₁ = (λ j → cong (SmashAssocIso .Iso.fun ∘ ((f ⋀→ (g ⋀→∙ h)))) (push (inr (inl tt)))
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

⋀SymmetricMonoidal : ∀ {ℓ} → isSymmetricMonoidal {ℓ} (_⋀∙_ {ℓ} {ℓ})
⊗fun ⋀SymmetricMonoidal = _⋀→∙_
⊗fun-id ⋀SymmetricMonoidal = ⋀→∙-idfun
⊗-comp ⋀SymmetricMonoidal = ⋀→∙-comp
⊗assoc ⋀SymmetricMonoidal = SmashAssocEquiv∙
⊗assoc-sq ⋀SymmetricMonoidal = ⋀assoc-sq
⊗pentagon ⋀SymmetricMonoidal = sym pentagon∙
⊗comm ⋀SymmetricMonoidal = Iso.fun ⋀CommIso , refl
⊗comm-sq ⋀SymmetricMonoidal f g = {!!}
hexagon ⋀SymmetricMonoidal = {!!}
⊗commid ⋀SymmetricMonoidal = {!!}
⊗Unit ⋀SymmetricMonoidal = {!!}
⊗lId ⋀SymmetricMonoidal = {!!}
⊗lId-sq ⋀SymmetricMonoidal = {!!}
⊗lId-assoc ⋀SymmetricMonoidal = {!!}
