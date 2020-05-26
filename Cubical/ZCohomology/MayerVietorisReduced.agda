
{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.MayerVietorisReduced where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Group.Base


open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''
    A' : Pointed ℓ
    B' : Pointed ℓ'


coHomFun : (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec setTruncIsSet λ β → ∣ β ∘ f ∣₀

module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  D : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  D = Pushout f g

  i : (n : ℕ) → coHom n D → coHom n A × coHom n B
  i zero = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                λ { δ →  ∣ (λ x → δ (inl x)) ∣₀ , ∣ (λ x → δ (inr x)) ∣₀}
  i (suc n) = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                   λ { δ →  ∣ (λ x → δ (inl x)) ∣₀ , ∣ (λ x → δ (inr x)) ∣₀}

  Δ : (n : ℕ) → coHom n A × coHom n B → coHom n C
  Δ n (α , β) = coHomFun n f α +ₕ -ₕ (coHomFun n g β)

  d-pre : (n : ℕ) → (C → coHomK n) → D → coHomK (suc n)
  d-pre n γ (inl x) = 0ₖ
  d-pre n γ (inr x) = 0ₖ
  d-pre zero γ (push a i) = Kn→ΩKn+1 zero (γ a) i
  d-pre (suc n) γ (push a i) = Kn→ΩKn+1 (suc n) (γ a) i
  
  d : (n : ℕ) → coHom n C → coHom (suc n) D
  d n = sRec setTruncIsSet λ a → ∣ d-pre n a ∣₀

  iIsHom : (n : ℕ) → isMorph (coHomGr n D) (×coHomGr n A B) (i n)
  iIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ f g → refl
  iIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ f g → refl


  prodElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : ∥ A ∥₀ × ∥ B ∥₀ → Type ℓ''}
          → ((x : ∥ A ∥₀ × ∥ B ∥₀) → isOfHLevel 2 (C x))
          → ((a : A) (b : B) → C (∣ a ∣₀ , ∣ b ∣₀))
          → (x : ∥ A ∥₀ × ∥ B ∥₀) → C x
  prodElim {A = A} {B = B} {C = C} hlevel ind (a , b) = schonf a b
    where
    schonf : (a : ∥ A ∥₀) (b : ∥ B ∥₀) → C (a , b)
    schonf = sElim (λ x → isOfHLevelΠ 2 λ y → hlevel (_ , _)) λ a → sElim (λ x → hlevel (_ , _))
                   λ b → ind a b


  prodElim2 : ∀ {ℓ ℓ' ℓ'' ℓ''' ℓ''''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
              {E : (∥ A ∥₀ × ∥ B ∥₀) → (∥ C ∥₀ × ∥ D ∥₀) → Type ℓ''''}
           → ((x : ∥ A ∥₀ × ∥ B ∥₀) (y : ∥ C ∥₀ × ∥ D ∥₀) → isOfHLevel 2 (E x y))
           → ((a : A) (b : B) (c : C) (d : D) → E (∣ a ∣₀ , ∣ b ∣₀) (∣ c ∣₀ , ∣ d ∣₀))
           → ((x : ∥ A ∥₀ × ∥ B ∥₀) (y : ∥ C ∥₀ × ∥ D ∥₀) → (E x y))
  prodElim2 isset f = prodElim (λ _ → isOfHLevelΠ 2 λ _ → isset _ _)
                               λ a b → prodElim (λ _ → isset _ _)
                                       λ c d → f a b c d

  ΔIsHom : (n : ℕ) → isMorph (×coHomGr n A B) (coHomGr n C) (Δ n)
  ΔIsHom zero = prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
                             λ f' x1 g' x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)
  ΔIsHom (suc n) = prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
                             λ f' x1 g' x2 → (λ i → ∣ (λ x → (f' (f x) +ₖ g' (f x)) +ₖ -distrₖ (x1 (g x)) (x2 (g x)) i) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ g' (f x)) (-ₖ x1 (g x)) (-ₖ x2 (g x)) (~ i)) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (g' (f x)) (-ₖ x1 (g x)) i +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → (f' (f x) +ₖ commₖ (g' (f x)) (-ₖ x1 (g x)) i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x)) (-ₖ x1 (g x)) (g' (f x)) (~ i) +ₖ (-ₖ x2 (g x))) ∣₀) ∙
                                                (λ i → ∣ (λ x → assocₖ (f' (f x) +ₖ (-ₖ x1 (g x))) (g' (f x))  (-ₖ x2 (g x)) i) ∣₀)

  dHomHelperPath : (n : ℕ) (h l : C → coHomK n) (a : C) → I → I → coHomK (suc n)
  dHomHelperPath n h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ 0ₖ (~ j)
                    ; (i = i1) → lUnitₖ 0ₖ (~ j)
                    ; (j = i0) → +ₖ→∙ n (h a) (l a) (~ k) i
                    ; (j = i1) → cong₂Funct (λ x y → x +ₖ y) (Kn→ΩKn+1 n (h a)) (Kn→ΩKn+1 n (l a)) (~ k) i})
          (bottom i j)
      where
      bottom : I → I → coHomK (suc n)
      bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ 0ₖ (~ j)
                                   ; (i = i1) → cong (λ x → lUnitₖ x (~ j)) (Kn→ΩKn+1 n (l a)) k})
                         (anotherbottom i j)
        where
        anotherbottom : I → I → coHomK (suc n)
        anotherbottom i j = hcomp (λ k → λ { (i = i0) → rUnitlUnit0 k (~ j)
                                            ; (i = i1) → rUnitlUnit0 k (~ j)
                                            ; (j = i0) → Kn→ΩKn+1 n (h a) i
                                            ; (j = i1) → cong (λ x → x +ₖ 0ₖ) (Kn→ΩKn+1 n (h a)) i})
                                  (cong (λ x → rUnitₖ x (~ j)) (Kn→ΩKn+1 n (h a)) i)


  dHomHelper : (n : ℕ) (h l : C → coHomK n) (x : D) → d-pre n (λ x → h x +ₖ l x) x ≡ d-pre n h x +ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (lUnitₖ 0ₖ)
  dHomHelper n h l (inr x) = sym (lUnitₖ 0ₖ)
  dHomHelper zero h l (push a i) j = dHomHelperPath zero h l a i j
  dHomHelper (suc n) h l (push a i) j = dHomHelperPath (suc n) h l a i j

  dIsHom : (n : ℕ) → isMorph (coHomGr n C) (coHomGr (suc n) D) (d n)
  dIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper zero f g x) i ∣₀
  dIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper (suc n) f g x) i ∣₀

  -- Long Exact Sequence

  Im-d⊂Ker-i : (n : ℕ) (x : coHom (suc n) D)
            → isInIm (coHomGr n C) (coHomGr (suc n) D) (d n) x
            → isInKer (coHomGr (suc n) D) (×coHomGr (suc n) A B) (i (suc n)) x
  Im-d⊂Ker-i n = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                       λ a → pElim (λ _ → isOfHLevelPath' 1 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                               (sigmaElim (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
                                λ δ b → (λ i → sElim (λ _ → isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                                                 (λ { δ → ∣ (λ x → δ (inl x)) ∣₀ , ∣ (λ x → δ (inr x)) ∣₀ }) (b (~ i))))

  Ker-i⊂Im-d : (n : ℕ) (x : coHom (suc n) D)
            → isInKer (coHomGr (suc n) D) (×coHomGr (suc n) A B) (i (suc n)) x
            → isInIm (coHomGr n C) (coHomGr (suc n) D) (d n) x
  Ker-i⊂Im-d n = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                       λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → 0ₖ} (isOfHLevelΠ 1 (λ _ → propTruncIsProp))
                                     (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn (sym (cong (λ F → F (f c)) p1)
                                                                                               ∙∙ cong a (push c)
                                                                                               ∙∙ cong (λ F → F (g c)) p2)) ∣₀
                                                                           , cong ∣_∣₀ (funExt (λ δ → helper n a p1 p2 δ)) ∣₋₁)
                                     (Iso.fun (PathIdTrunc₀Iso) (cong proj₁ p))
                                     (Iso.fun (PathIdTrunc₀Iso) (cong proj₂ p))
    where
      pushFiller : (n : ℕ) (F : D → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n))
                (p1 : Path (_ → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) (λ a₁ → F (inl a₁)) (λ _ → ∣ north ∣))
                (p2 : Path (_ → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) (λ a₁ → F (inr a₁)) (λ _ → ∣ north ∣)) →
                (c : C) → I → I → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)
      pushFiller n F p1 p2 c i j =
        hcomp (λ k → λ { (i = i1) → F (push c j)
                        ; (j = i0) → p1 (~ i ∧ k) (f c)
                        ; (j = i1) → p2 (~ i ∧ k) (g c)})
              (F (push c j))
      helper : (n : ℕ) (F : D → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n))
               (p1 : Path (_ → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) (λ a₁ → F (inl a₁)) (λ _ → ∣ north ∣))
               (p2 : Path (_ → ∥ S₊ (suc n) ∥ ℕ→ℕ₋₂ (suc n)) (λ a₁ → F (inr a₁)) (λ _ → ∣ north ∣)) →
               (δ : D) → d-pre n (λ c → ΩKn+1→Kn ((λ i₁ → p1 (~ i₁) (f c))
                                                     ∙∙ cong F (push c)
                                                     ∙∙ cong (λ F → F (g c)) p2)) δ
                        ≡ F δ
      helper n F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
      helper n F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
      helper zero F p1 p2 (push a i) j = 
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                        ; (i = i1) → p2 (~ j) (g a)
                        ; (j = i0) → Iso.rightInv (Iso3-Kn-ΩKn+1 zero) ((λ i₁ → p1 (~ i₁) (f a))
                                                                       ∙∙ cong F (push a)
                                                                       ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
                        ; (j = i1) → F (push a i)})
              (pushFiller zero F p1 p2 a j i)
      helper (suc n) F p1 p2 (push a i) j =
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                        ; (i = i1) → p2 (~ j) (g a)
                        ; (j = i0) → Iso.rightInv (Iso3-Kn-ΩKn+1 (suc n)) ((λ i₁ → p1 (~ i₁) (f a))
                                                                           ∙∙ cong F (push a)
                                                                           ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
                        ; (j = i1) → F (push a i)})
              (pushFiller (suc n) F p1 p2 a j i)

  Im-i⊂Ker-Δ : (n : ℕ) (x : coHom n A × coHom n B)
            → isInIm (coHomGr n D) (×coHomGr n A B) (i n) x
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) x
  Im-i⊂Ker-Δ n (Fa , Fb) =
    sElim {B = λ Fa → (Fb : _) → isInIm (coHomGr n D) (×coHomGr n A B) (i n) (Fa , Fb)
                                → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) (Fa , Fb)}
          (λ _ → isOfHLevelΠ 2 λ _ → (isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _))
          (λ Fa → sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                        λ Fb → pRec (setTruncIsSet _ _)
                                     (sigmaElim (λ x → isOfHLevelSuc 1 (setTruncIsSet _ _))
                                                λ Fd p → helper n Fa Fb Fd p))
          Fa
          Fb
    where
    helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n) (Fd : D → coHomK n)
          → (i n ∣ Fd ∣₀ ≡ (∣ Fa ∣₀ , ∣ Fb ∣₀))
          → (Δ n) (∣ Fa ∣₀ , ∣ Fb ∣₀) ≡ 0ₕ
    helper zero Fa Fb Fd p = cong (Δ zero) (sym p)
                           ∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₀ +ₕ -ₕ ∣ (λ x → Fd (push x (~ i))) ∣₀)
                           ∙ rCancelₕ ∣ (λ x → Fd (inl (f x))) ∣₀
    helper (suc n) Fa Fb Fd p = cong (Δ (suc n)) (sym p)
                              ∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₀ +ₕ -ₕ ∣ (λ x → Fd (push x (~ i))) ∣₀)
                              ∙ rCancelₕ ∣ (λ x → Fd (inl (f x))) ∣₀

  

  Ker-Δ⊂Im-i : (n : ℕ) (a : coHom n A × coHom n B)
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) a
            → isInIm (coHomGr n D) (×coHomGr n A B) (i n) a
  Ker-Δ⊂Im-i n (Fa , Fb) =
    sElim {B = λ Fa → (Fb : _) → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) (Fa , Fb)
                                → isInIm (coHomGr n D) (×coHomGr n A B) (i n) (Fa , Fb)}
          (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          (λ Fa → sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                         λ Fb p → pRec propTruncIsProp
                                        (λ q → ∣ ∣ helpFun n Fa Fb (funExt⁻ q) ∣₀
                                                , anotherHelper n Fa Fb q ∣₋₁)
                                        (helper n Fa Fb p))
          Fa
          Fb

    where
    helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
           → (Δ n) (∣ Fa ∣₀ , ∣ Fb ∣₀) ≡ 0ₕ
           → ∥  (Path (_ → _) (λ c → Fa (f c)) (λ c → Fb (g c))) ∥₋₁
    helper zero Fa Fb p = Iso.fun (PathIdTrunc₀Iso)
                                   (sym (rUnitₕ (coHomFun zero f ∣ Fa ∣₀))
                                 ∙ (λ i → coHomFun zero f ∣ Fa ∣₀ +ₕ (lCancelₕ (coHomFun zero g ∣ Fb ∣₀) (~ i)))
                                 ∙ sym (assocₕ (coHomFun zero f ∣ Fa ∣₀) (-ₕ (coHomFun zero g ∣ Fb ∣₀)) (coHomFun zero g ∣ Fb ∣₀))
                                 ∙ cong (λ x → x +ₕ (coHomFun zero g ∣ Fb ∣₀)) p
                                 ∙ lUnitₕ (coHomFun zero g ∣ Fb ∣₀))
    helper (suc n) Fa Fb p = Iso.fun (PathIdTrunc₀Iso)
                                      (sym (rUnitₕ (coHomFun (suc n) f ∣ Fa ∣₀))
                                    ∙ (λ i → coHomFun (suc n) f ∣ Fa ∣₀ +ₕ (lCancelₕ (coHomFun (suc n) g ∣ Fb ∣₀) (~ i)))
                                    ∙ sym (assocₕ (coHomFun (suc n) f ∣ Fa ∣₀) (-ₕ (coHomFun (suc n) g ∣ Fb ∣₀)) (coHomFun (suc n) g ∣ Fb ∣₀))
                                    ∙ cong (λ x → x +ₕ (coHomFun (suc n) g ∣ Fb ∣₀)) p
                                    ∙ lUnitₕ (coHomFun (suc n) g ∣ Fb ∣₀))

    helpFun : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
            → ((c : C) → Fa (f c) ≡ Fb (g c))
            → D → coHomK n
    helpFun n Fa Fb p (inl x) = Fa x
    helpFun n Fa Fb p (inr x) = Fb x
    helpFun n Fa Fb p (push a i) = p a i

    anotherHelper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
                 → (q : Path (C → coHomK n) (λ c → Fa (f c)) (λ c → Fb (g c)))
                 → i n ∣ helpFun n Fa Fb (λ x i₁ → q i₁ x) ∣₀ ≡ (∣ Fa ∣₀ , ∣ Fb ∣₀)
    anotherHelper zero Fa Fb q = refl
    anotherHelper (suc n) Fa Fb q = refl


  Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n C)
             → isInKer (coHomGr n C) (coHomGr (suc n) D) (d n) a
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  Ker-d⊂Im-Δ n =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn (cong (λ f → f (inl a)) p)) ∣₀ ,
                                                     ∣ (λ b → ΩKn+1→Kn (cong (λ f → f (inr b)) p)) ∣₀) ,
                                                  Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 n Fc p c) ∣₋₁ ∣₋₁)
                                         (Iso.fun (PathIdTrunc₀Iso) p)

    where
    distrHelper : (n : ℕ) (p q : _) → ΩKn+1→Kn {n = n} p +ₖ (-ₖ ΩKn+1→Kn q) ≡ ΩKn+1→Kn (p ∙ sym q)
    distrHelper n p q i = ΩKn+1→Kn (Iso.rightInv (Iso3-Kn-ΩKn+1 n) p i ∙ Iso.rightInv (Iso3-Kn-ΩKn+1 n) (sym (Iso.rightInv (Iso3-Kn-ΩKn+1 n) q i)) i)


    helper2 : (n : ℕ) (Fc : C → coHomK n) (p : d-pre n Fc ≡ (λ _ → ∣ north ∣)) (c : C)
            → ΩKn+1→Kn (λ i₁ → p i₁ (inl (f c))) +ₖ (-ₖ ΩKn+1→Kn (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
    helper2 zero Fc p c = distrHelper zero (cong (λ F → F (inl (f c))) p) (cong (λ F → F (inr (g c))) p)
                        ∙ cong ΩKn+1→Kn (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
                                                ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
                                                ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
                        ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 zero) (Fc c)
    helper2 (suc n) Fc p c = distrHelper (suc n) (cong (λ F → F (inl (f c))) p) (cong (λ F → F (inr (g c))) p)
                           ∙ cong ΩKn+1→Kn (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
                                                   ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
                                                   ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
                           ∙ Iso.leftInv (Iso3-Kn-ΩKn+1 (suc n)) (Fc c)

  Im-Δ⊂Ker-d : (n : ℕ) (a : coHom n C)
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
             → isInKer (coHomGr n C) (coHomGr (suc n) D) (d n) a
  Im-Δ⊂Ker-d n =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ Fc → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
                       (sigmaProdElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                      λ Fa Fb p → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
                                                        (λ q → ((λ i → d n ∣ (q (~ i)) ∣₀) ∙ dΔ-Id n Fa Fb))
                                                        (Iso.fun (PathIdTrunc₀Iso) p))

    where

    d-preLeftId : (n : ℕ) (Fa : A → coHomK n)(d : D)
                → d-pre n (Fa ∘ f) d ≡ 0ₖ
    d-preLeftId n Fa (inl x) = Kn→ΩKn+1 n (Fa x)
    d-preLeftId n Fa (inr x) = refl
    d-preLeftId zero Fa (push a i) j = Kn→ΩKn+1 zero (Fa (f a)) (j ∨ i)
    d-preLeftId (suc n) Fa (push a i) j = Kn→ΩKn+1 (suc n) (Fa (f a)) (j ∨ i)

    d-preRightId : (n : ℕ) (Fb : B → coHomK n) (d : D)
                → d-pre n (Fb ∘ g) d ≡ 0ₖ
    d-preRightId n Fb (inl x) = refl
    d-preRightId n Fb (inr x) = sym (Kn→ΩKn+1 n (Fb x))
    d-preRightId zero Fb (push a i) j = Kn→ΩKn+1 zero (Fb (g a)) (~ j ∧ i)
    d-preRightId (suc n) Fb (push a i) j = Kn→ΩKn+1 (suc n) (Fb (g a)) (~ j ∧ i)

    dΔ-Id : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
            → d n (Δ n (∣ Fa ∣₀ , ∣ Fb ∣₀)) ≡ 0ₕ
    dΔ-Id zero Fa Fb =
      dIsHom zero ∣ (λ x → Fa (f x)) ∣₀ (-ₕ ∣ (λ x → Fb (g x)) ∣₀)
     ∙ (λ i → d zero ∣ (λ x → Fa (f x)) ∣₀ +ₕ morphMinus (coHomGr zero C) (coHomGr 1 D) (d zero) (dIsHom zero) ∣ (λ x → Fb (g x)) ∣₀ i)
     ∙ (λ i → d zero ∣ (λ x → Fa (f x)) ∣₀ +ₕ -ₕ (d zero ∣ (λ x → Fb (g x)) ∣₀))
     ∙ (λ i → ∣ funExt (d-preLeftId zero Fa) i ∣₀ +ₕ -ₕ ∣ funExt (d-preRightId zero Fb) i ∣₀)
     ∙ rCancelₕ 0ₕ
    dΔ-Id (suc n) Fa Fb =
      dIsHom (suc n) ∣ (λ x → Fa (f x)) ∣₀ (-ₕ ∣ (λ x → Fb (g x)) ∣₀)
     ∙ (λ i → d (suc n) ∣ (λ x → Fa (f x)) ∣₀ +ₕ morphMinus (coHomGr (suc n) C) (coHomGr (2 + n) D) (d (suc n)) (dIsHom (suc n)) ∣ (λ x → Fb (g x)) ∣₀ i)
     ∙ (λ i → d (suc n) ∣ (λ x → Fa (f x)) ∣₀ +ₕ -ₕ (d (suc n) ∣ (λ x → Fb (g x)) ∣₀))
     ∙ (λ i → ∣ funExt (d-preLeftId (suc n) Fa) i ∣₀ +ₕ -ₕ ∣ funExt (d-preRightId (suc n) Fb) i ∣₀)
     ∙ rCancelₕ 0ₕ
