{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.Pentagon where

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

-- pentagon identity for smash products
module _ {ℓ ℓ' ℓ'' ℓ''' : Level}
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''} {D : Pointed ℓ'''}
  where
  assc₁∙ : (A ⋀∙ (B ⋀∙ (C ⋀∙ D))) →∙ ((A ⋀∙ B) ⋀∙ (C ⋀∙ D))
  assc₁∙ = ≃∙map SmashAssocEquiv∙
  assc₁ = fst assc₁∙

  assc₂∙ : ((A ⋀∙ B) ⋀∙ (C ⋀∙ D)) →∙ (((A ⋀∙ B) ⋀∙ C) ⋀∙ D)
  assc₂∙ = ≃∙map SmashAssocEquiv∙
  assc₂ = fst assc₂∙

  asscᵣ = assc₂ ∘ assc₁
  asscᵣ∙ = assc₂∙ ∘∙ assc₁∙

  assc₃∙ : A ⋀∙ (B ⋀∙ (C ⋀∙ D)) →∙ A ⋀∙ ((B ⋀∙ C) ⋀∙ D)
  assc₃∙ = (idfun∙ A) ⋀→∙ (≃∙map SmashAssocEquiv∙)
  assc₃ = fst assc₃∙

  assc₄∙ : A ⋀∙ ((B ⋀∙ C) ⋀∙ D) →∙ (A ⋀∙ (B ⋀∙ C)) ⋀∙ D
  assc₄∙ = ≃∙map SmashAssocEquiv∙
  assc₄ = fst assc₄∙

  assc₅∙ : (A ⋀∙ (B ⋀∙ C)) ⋀∙ D →∙ ((A ⋀∙ B) ⋀∙ C) ⋀∙ D
  assc₅∙ = ≃∙map SmashAssocEquiv∙ ⋀→∙ idfun∙ D
  assc₅ = fst assc₅∙

  asscₗ = assc₅ ∘ assc₄ ∘ assc₃
  asscₗ∙ = assc₅∙ ∘∙ (assc₄∙ ∘∙ assc₃∙)

  -- pointed version
  pentagon∙main : Σ[ f ∈ ((x : A ⋀ (B ⋀∙ (C ⋀∙ D))) → asscₗ x ≡ asscᵣ x) ]
                   f (inl tt) ≡ refl
  pentagon∙main =
    (⋀-fun≡'.main {A = A} {B = (B ⋀∙ (C ⋀∙ D))} _ _
      (λ x → main₁ (fst x) (snd x))
      (λ x → p≡refl
           ◁ ((λ i j → assc₅ (assc₄ (rUnit (push (inl x)) (~ j) i)))
           ▷ sym (main₁≡refl x)))
      (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
        λ x y → funExt⁻ (cong fst (to→∙ₗ≡to→∙ᵣ x)) y ∙ sym p≡refl)
        , p≡refl)
    where
    module lemmas₁ (x : typ A) (y : typ B) where
      module N = ⋀-fun≡' (λ z → asscₗ (inr (x , inr (y , z))))
                          (λ z → asscᵣ (inr (x , inr (y , z))))
                          (λ _ → refl)
      open N
      assc-r-r-p-l : (c : _)
        → cong asscₗ (λ i → (inr (x , inr (y , push (inl c) i))))
         ≡ cong asscᵣ (λ i → (inr (x , inr (y , push (inl c) i))))
      assc-r-r-p-l c = sym (rUnit _)

      assc-r-r-p-r  : (d : _)
        → cong asscₗ (λ i → (inr (x , inr (y , push (inr d) i))))
         ≡ cong asscᵣ (λ i → (inr (x , inr (y , push (inr d) i))))
      assc-r-r-p-r  d = cong (cong (assc₅ ∘ assc₄)) lem₁
             ∙ cong (cong assc₅) lem₂
             ∙ lem₃
             ∙ sym lem₄
        where
        lem₁ : cong assc₃ (λ i → (inr (x , inr (y , push (inr d) i))))
          ≡ (λ j → inr (x , push (inr d) j))
           ∙ λ j → inr (x , inr ((push (inl y) j) , d))
        lem₁ = (λ k i → inr (x , Iso.fun ⋀CommIso
                (compPath≡compPath'
                  (push (inl d))
                  (λ i → inr (d , push (inl y) i)) (~ k) i)))
           ∙ (λ k i → inr (x , cong-∙ (Iso.fun ⋀CommIso)
                        (push (inl d))
                        (λ i → inr (d , push (inl y) i)) k i))
           ∙ cong-∙ (λ y → inr (x , y))
              (push (inr d))
              λ i → inr (push (inl y) i , d)

        lem₂ :
            cong assc₄ ((λ j → inr (x , push (inr d) j))
                    ∙ λ j → inr (x , inr ((push (inl y) j) , d)))
          ≡ ((push (inr d) ∙ (λ i → inr (push (inl x) i , d))) ∙
             (λ i → inr (inr (x , push (inl y) i) , d)))
        lem₂ = cong-∙ assc₄ (λ j → inr (x , push (inr d) j))
                           (λ j → inr (x , inr ((push (inl y) j) , d)))
             ∙ cong (_∙ (λ i → inr (inr (x , push (inl y) i) , d)))
                    ((cong (cong (Iso.fun ⋀CommIso))
                       (sym (compPath≡compPath'
                        (push (inl d)) (λ i → inr (d , push (inl x) i))))
                    ∙ cong-∙ (Iso.fun ⋀CommIso)
                        (push (inl d))
                        λ i → inr (d , push (inl x) i))
                   ∙ λ _ → push (inr d) ∙ λ i → inr ((push (inl x) i) , d))

        lem₃ : cong assc₅ (((push (inr d) ∙ (λ i → inr (push (inl x) i , d)))
                         ∙ (λ i → inr (inr (x , push (inl y) i) , d))))
           ≡ ((λ i → push (inr d) i)
            ∙ (λ i → inr (push (inl (inr (x , y))) i , d)))
        lem₃ = cong-∙ assc₅ ((push (inr d)
                          ∙ (λ i → inr (push (inl x) i , d))))
                          (λ i → inr (inr (x , push (inl y) i) , d))
             ∙ cong₂ _∙_
                 (cong-∙ assc₅
                         (push (inr d))
                         (λ i → inr (push (inl x) i , d))
               ∙ cong₂ _∙_ (sym (rUnit (push (inr d))))
                           refl
               ∙ sym (rUnit (push (inr d))))
                 (λ _ i → inr (push (inl (inr (x , y))) i , d))

        lem₄ : cong asscᵣ (λ i → (inr (x , inr (y , push (inr d) i))))
          ≡ ((λ i → push (inr d) i)
            ∙ (λ i → inr (push (inl (inr (x , y))) i , d)))
        lem₄ = (λ _ i → assc₂ (inr (inr (x , y) , push (inr d) i)))
           ∙ (cong (cong (Iso.fun (⋀CommIso)))
                (cong (cong (Iso.inv (Iso-⋀-⋀×2 D (A ⋀∙ B) C)))
                  (refl {x = sym (gluel d (inr (x , y))) }))
           ∙ cong-∙∙ (Iso.fun (⋀CommIso))
               (push (inl d))
               (λ i → inr (d , push (inl (inr (x , y))) i))
               refl)
           ∙ sym (compPath≡compPath' _ _)

      p≡refl : p ≡ refl
      p≡refl = p≡p'
          ∙ (λ j → assc-r-r-p-l (pt C) j ∙∙ refl ∙∙ sym (assc-r-r-p-l (pt C) i1))
          ∙ ∙∙lCancel _

    main₂ : (x : typ A) (y : typ B) (c : (C ⋀ D))
      → asscₗ (inr (x , inr (y , c)))
       ≡ asscᵣ (inr (x , inr (y , c)))
    main₂ x y = ⋀-fun≡'.main {A = C} {B = D} _ _
      (λ _ → refl)
      (λ c → lemmas₁.p≡refl x y ◁ flipSquare (lemmas₁.assc-r-r-p-l x y c))
      (→∙Homogeneous≡ (isHomogeneousPath _ _)
        (funExt λ d → ((λ j → lemmas₁.assc-r-r-p-r  x y d j
                    ∙∙ refl
                    ∙∙ (λ i → asscᵣ (inr (x
                      , inr (y , push (inr d) (~ i))))))
                      ∙ ∙∙lCancel _)
                      ∙ sym (lemmas₁.p≡refl x y)))

    module lemmas₂ (x : typ A) where
      module K = ⋀-fun≡' (λ z → asscₗ (inr (x , z)))
       (λ z → asscᵣ (inr (x , z)))
       (λ y₁ → main₂ x (fst y₁) (snd y₁))
      open K
      main₂∙ : (y : _) → main₂ x y (pt (C ⋀∙ D)) ≡ refl
      main₂∙ y = (λ i → lemmas₁.assc-r-r-p-r  x y (pt D) i
                 ∙∙ refl
                 ∙∙ sym (lemmas₁.assc-r-r-p-r  x y (pt D) i1))
          ∙ ∙∙lCancel _

      assc-r-p-r-r  : (c : _) (d : _)
        → cong asscₗ (λ i → inr (x , push (inr (inr (c , d))) i))
         ≡ cong asscᵣ (λ i → inr (x , push (inr (inr (c , d))) i))
      assc-r-p-r-r  c d = cong (cong assc₅) (cong (cong assc₄) lem₁ ∙ lem₂)
                ∙∙ lem₃
                ∙∙ sym
                   (cong (cong assc₂) lem₄ ∙ lem₅)

        where
        lem₄ : cong assc₁ (λ i → inr (x , push (inr (inr (c , d))) i))
           ≡ push (inr (inr (c , d)))
            ∙ (λ i → inr (push (inl x) i , inr (c , d)))
        lem₄ = cong-∙∙ (Iso.fun ⋀CommIso)
                (push (inl (inr (c , d))))
                (λ i → inr (inr (c , d) , push (inl x) i))
                refl
           ∙ sym (compPath≡compPath'
                 (push (inr (inr (c , d))))
                 λ i → inr (push (inl x) i , inr (c , d)))

        lem₅ : cong assc₂ (push (inr (inr (c , d)))
            ∙ (λ i → inr (push (inl x) i , inr (c , d))))
            ≡ (push (inr d) ∙ (λ i → inr ((push (inr c)
             ∙ λ j → inr (push (inl x) j , c)) i , d)))
        lem₅ = cong-∙ assc₂
               (push (inr (inr (c , d))))
               (λ i → inr (push (inl x) i , inr (c , d)))
          ∙∙ cong₂ _∙_
               (cong-∙∙ (Iso.fun ⋀CommIso)
                 (push (inl d))
                 (λ i → inr (d , push (inr c) i)) refl
              ∙ sym (compPath≡compPath' (push (inr d))
                 λ i → inr (push (inr c) i , d)))
               (λ _ → (λ i → inr (inr (push (inl x) i , c) , d)))
          ∙∙ (sym (assoc (push (inr d)) _ _)
           ∙ cong (push (inr d) ∙_)
               (sym (cong-∙ (λ a → inr (a , d))
                 (push (inr c))
                 λ i → inr (push (inl x) i , c))))

        lem₁ : cong assc₃ (λ i → inr (x , push (inr (inr (c , d))) i))
          ≡ (λ i → inr (x , (push (inr d) i)))
          ∙ (λ i → inr (x , inr (push (inr c) i , d)))
        lem₁ = (λ k i → inr (x
              , (cong-∙∙ (Iso.fun ⋀CommIso)
                   (push (inl d)) (λ i → inr (d , push (inr c) i)) refl
              ∙ sym (compPath≡compPath'
                      (push (inr d))
                      λ i → inr (push (inr c) i , d))) k i))
           ∙ cong-∙ (λ y → inr (x , y))
                    (push (inr d))
                    (λ i → inr (push (inr c) i , d))

        lem₂ : cong assc₄ ((λ i → inr (x , (push (inr d) i)))
                      ∙ (λ i → inr (x , inr (push (inr c) i , d))))
            ≡ (push (inr d) ∙ (λ i → inr (push (inl x) i , d)))
            ∙ (λ i → inr (inr (x , push (inr c) i) , d))
        lem₂ = cong-∙ assc₄
               (λ i → inr (x , (push (inr d) i)))
              (λ i → inr (x , inr (push (inr c) i , d)))
           ∙ cong₂ _∙_
                (cong-∙∙ (Iso.fun ⋀CommIso)
                  (push (inl d))
                  (λ i → inr (d , push (inl x) i))
                  refl
              ∙ sym (compPath≡compPath'
                     (push (inr d))
                     λ i → inr (push (inl x) i , d)))
                (λ k → (λ i → inr (inr (x , push (inr c) i) , d)))

        lem₃ : cong assc₅
              ((push (inr d) ∙ (λ i → inr (push (inl x) i , d)))
               ∙ (λ i → inr (inr (x , push (inr c) i) , d)))
           ≡ push (inr d) ∙ (λ i → inr ((push (inr c)
             ∙ λ j → inr (push (inl x) j , c)) i , d))
        lem₃ = cong-∙ assc₅
              (push (inr d) ∙ (λ i → inr (push (inl x) i , d)))
              (λ i → inr (inr (x , push (inr c) i) , d))
           ∙ cong₂ _∙_
                (cong-∙ assc₅ (push (inr d)) (λ i → inr (push (inl x) i , d))
                      ∙ cong₂ _∙_ (sym (rUnit (push (inr d)))) refl
                      ∙ sym (rUnit (push (inr d))))
               (λ k i → inr
                 ((cong-∙∙ (Iso.fun ⋀CommIso)
                    (push (inl c))
                    (λ i → inr (c , push (inl x) i))
                    refl
                 ∙ sym (compPath≡compPath'
                       (push (inr c))
                       λ i → inr (push (inl x) i , c))) k i , d))

      assc-r-p-r-l : cong asscₗ (λ i → inr (x , push (inr (inl tt)) i))
           ≡ cong asscᵣ (λ i → inr (x , push (inr (inl tt)) i))
      assc-r-p-r-l = sym
        (cong (cong assc₂)
          (cong-∙∙ (Iso.fun ⋀CommIso)
            (push (inl (inl tt)))
            (λ i → inr (inl tt , push (inl x) i))
            refl
         ∙ sym (compPath≡compPath' (push (inr (inl tt)))
                λ i → inr ((push (inl x) i) , (inl tt))))
          ∙∙ cong-∙ assc₂ (push (inr (inl tt)))
                         (λ i → inr ((push (inl x) i) , (inl tt)))
          ∙∙ sym (rUnit refl))

      p≡refl : p ≡ refl
      p≡refl =
          (λ i → assc-r-p-r-l i
               ∙∙ main₂∙ (pt B) i
               ∙∙ sym (assc-r-p-r-l i1))
        ∙ ∙∙lCancel _

    main₁ : (x : typ A) (y : B ⋀ (C ⋀∙ D))
      → asscₗ (inr (x , y)) ≡ asscᵣ (inr (x , y))
    main₁ x = ⋀-fun≡'.main {A = B} {B = (C ⋀∙ D)} _ _
      (λ y → main₂ x (fst y) (snd y))
      (λ y → (lemmas₂.p≡refl x ∙ sym (lemmas₂.main₂∙ x y)))
      (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
        λ c d → ((λ i → lemmas₂.assc-r-p-r-r  x c d i
                       ∙∙ refl
                       ∙∙ sym (lemmas₂.assc-r-p-r-r  x c d i1))
               ∙ ∙∙lCancel _)
          ∙ sym (lemmas₂.p≡refl x))

    main₁⋆ : (x : fst B) → main₁ (pt A) (inr (x , (inl tt))) ≡ refl
    main₁⋆ x =
      (λ i → lemmas₁.assc-r-r-p-r  (pt A) x (pt D) i
           ∙∙ refl
           ∙∙ sym (lemmas₁.assc-r-r-p-r  (pt A) x (pt D) i1))
      ∙ ∙∙lCancel _

    assc-p-r-r-l : (x : fst B)
      → cong asscₗ (push (inr (inr (x , inl tt))))
       ≡ cong asscᵣ (push (inr (inr (x , inl tt))))
    assc-p-r-r-l x =
      cong (cong (assc₅ ∘ assc₄)) (sym (rUnit (push (inr (inl tt)))))
         ∙ sym (cong (cong assc₂)
                 (cong-∙∙ (Iso.fun ⋀CommIso) (push (inl (inl tt)))
                          (λ i → inr (inl tt , push (inr x) i)) refl
                ∙ sym (compPath≡compPath'
                      (push (inr (inl tt)))
                      λ i → inr (push (inr x) i , inl tt)))
              ∙ cong-∙ assc₂ (push (inr (inl tt)))
                            (λ i → inr (push (inr x) i , inl tt))
              ∙ sym (rUnit refl))

    to→∙ₗ : (x : fst B)
      → (C ⋀∙ D)
      →∙ (Path (((A ⋀∙ B) ⋀∙ C) ⋀ D) (inl tt) (inl tt) , refl)
    fst (to→∙ₗ x) y = ((λ i → asscₗ (push (inr (inr (x , y))) i))
       ∙∙ main₁ (pt A) (inr (x , y))
       ∙∙ (λ i → asscᵣ (push (inr (inr (x , y))) (~ i))))
    snd (to→∙ₗ x) =
        (λ j → assc-p-r-r-l x j
             ∙∙ main₁⋆ x j
             ∙∙ sym (assc-p-r-r-l x i1))
      ∙ ∙∙lCancel _

    to→∙ᵣ : (x : fst B)
      → (C ⋀∙ D)
      →∙ (Path (((A ⋀∙ B) ⋀∙ C) ⋀ D) (inl tt) (inl tt) , refl)
    fst (to→∙ᵣ x) y = refl
    snd (to→∙ᵣ x) = refl

    module L = ⋀-fun≡' asscₗ asscᵣ (λ x₁ → main₁ (fst x₁) (snd x₁))
    open L
    main₁≡refl : (x : _) → main₁ x (inl tt) ≡ refl
    main₁≡refl x = (λ i → lemmas₂.assc-r-p-r-l x i
                       ∙∙ lemmas₂.main₂∙ x (pt B) i
                       ∙∙ sym (lemmas₂.assc-r-p-r-l x i1))
                ∙ ∙∙lCancel _

    assc-p-r-l : cong asscₗ (push (inr (inl tt)))
               ≡ cong asscᵣ (push (inr (inl tt)))
    assc-p-r-l i = cong (assc₅ ∘ assc₄) (rUnit (push (inr (inl tt))) (~ i))

    p≡refl : p ≡ refl
    p≡refl =
        (λ i → assc-p-r-l i ∙∙ main₁≡refl (pt A) i ∙∙ sym (assc-p-r-l i1))
      ∙ ∙∙lCancel _

    main₁-lem∞ : (x : fst B) (c : fst C) (d : fst D)
      → main₁ (pt A) (inr (x , inr (c , d))) ≡ refl
    main₁-lem∞ = λ _ _ _ → refl

    assc-p-r-r-r : (x : fst B) (c : fst C) (d : fst D)
      → cong asscₗ (push (inr (inr (x , inr (c , d)))))
      ≡ cong asscᵣ (push (inr (inr (x , inr (c , d)))))
    assc-p-r-r-r x c d =
         cong (cong (assc₅ ∘ assc₄))
              (sym (rUnit (push (inr (inr (inr (x , c) , d))))))
      ∙∙ cong (cong assc₅)
              (cong-∙∙ (Iso.fun ⋀CommIso) (push (inl d))
                       (λ i → inr (d , push (inr (inr (x , c))) i)) refl
                ∙ sym (compPath≡compPath' (push (inr d))
                      λ i → inr (push (inr (inr (x , c))) i , d)))
            ∙ (cong-∙ assc₅ (push (inr d))
                      λ i → inr (push (inr (inr (x , c))) i , d))
      ∙∙ (cong₂ _∙_ (sym (rUnit (push (inr d))))
                    (λ k i → inr ((cong-∙∙ (Iso.fun ⋀CommIso) (push (inl c))
                              (λ i → inr (c , push (inr x) i)) refl
                     ∙ sym (compPath≡compPath'
                              (push (inr c))
                              λ i → inr (push (inr x) i , c))) k i , d))
       ∙ sym (cong (cong assc₂)
                   (cong-∙∙ (Iso.fun ⋀CommIso) (push (inl (inr (c , d))))
                                     (λ i → inr (inr (c , d) , push (inr x) i))
                                     refl
                  ∙ sym (compPath≡compPath'
                          (push (inr (inr (c , d))))
                          λ i → inr (push (inr x) i , inr (c , d))))
           ∙∙ cong-∙ assc₂ (push (inr (inr (c , d))))
                          (λ i → inr (push (inr x) i , inr (c , d)))
           ∙∙ (cong₂ _∙_
                (cong-∙∙ (Iso.fun ⋀CommIso)
                  (push (inl d)) (λ i → inr (d , push (inr c) i)) refl
                  ∙ sym (compPath≡compPath' (push (inr d))
                        λ i → inr (push (inr c) i , d)))
               refl
            ∙ sym (assoc (push (inr d)) _ _)
            ∙ cong (push (inr d) ∙_)
               (sym (cong-∙ (λ a → inr (a , d)) (push (inr c))
               λ i → inr (push (inr x) i , c))))))

    to→∙ₗ≡to→∙ᵣ : (x : fst B) → to→∙ₗ x ≡ to→∙ᵣ x
    to→∙ₗ≡to→∙ᵣ x = ⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
      λ c d → (λ i → assc-p-r-r-r x c d i
                    ∙∙ refl
                    ∙∙ sym (assc-p-r-r-r x c d i1))
             ∙ ∙∙lCancel _

  -- plain penetagon
  pentagon : (x : A ⋀ (B ⋀∙ (C ⋀∙ D))) → asscₗ x ≡ asscᵣ x
  pentagon x = fst pentagon∙main x

  -- pointed pentagon
  pentagon∙ : asscₗ∙ ≡ asscᵣ∙
  pentagon∙ =
    ΣPathP ((funExt pentagon)
         , (flipSquare (snd pentagon∙main
         ◁ flipSquare (sym (rUnit _)))))
