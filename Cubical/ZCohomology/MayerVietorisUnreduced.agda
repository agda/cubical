{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.MayerVietorisUnreduced where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)

open GroupHom

module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  -- Proof from Brunerie 2016.
  -- We first define the three morphisms involved: i, Δ and d.

  private
    i* : (n : ℕ) → coHom n (Pushout f g) → coHom n A × coHom n B
    i* n = sRec (isSet× setTruncIsSet setTruncIsSet) λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂

  iIsHom : (n : ℕ) → isGroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B) (i* n)
  iIsHom n = sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _) λ _ _ → refl

  i : (n : ℕ) → GroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B)
  GroupHom.fun (i n) = i* n
  GroupHom.isHom (i n) = iIsHom n

  private
    distrLem : (n : ℕ) (x y z w : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ (z +[ n ]ₖ w) ≡ (x -[ n ]ₖ z) +[ n ]ₖ (y -[ n ]ₖ w)
    distrLem n x y z w = cong (λ z → (x +[ n ]ₖ y) +[ n ]ₖ z) (-distrₖ n z w)
                     ∙∙ sym (assocₖ n x y ((-[ n ]ₖ z) +[ n ]ₖ (-[ n ]ₖ w)))
                     ∙∙ cong (λ y → x +[ n ]ₖ y) (commₖ n y ((-[ n ]ₖ z) +[ n ]ₖ (-[ n ]ₖ w)) ∙ sym (assocₖ n _ _ _))
                     ∙∙ assocₖ n _ _ _
                     ∙∙ cong (λ y → (x -[ n ]ₖ z) +[ n ]ₖ y) (commₖ n (-[ n ]ₖ w) y)

    Δ' : (n : ℕ) → coHom n A × coHom n B → coHom n C
    Δ' n (α , β) = coHomFun n f α -[ n ]ₕ coHomFun n g β

    Δ'-isMorph : (n : ℕ) → isGroupHom (×coHomGr n A B) (coHomGr n C) (Δ' n)
    Δ'-isMorph n =
      prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
        λ f' x1 g' x2 i → ∣ (λ x → distrLem n (f' (f x)) (g' (f x)) (x1 (g x)) (x2 (g x)) i) ∣₂

  Δ : (n : ℕ) → GroupHom (×coHomGr n A B) (coHomGr n C)
  GroupHom.fun (Δ n) = Δ' n
  GroupHom.isHom (Δ n) = Δ'-isMorph n

  d-pre : (n : ℕ) → (C → coHomK n) → Pushout f g → coHomK (suc n)
  d-pre n γ (inl x) = 0ₖ (suc n)
  d-pre n γ (inr x) = 0ₖ (suc n)
  d-pre n γ (push a i) = Kn→ΩKn+1 n (γ a) i

  dHomHelper : (n : ℕ) (h l : C → coHomK n) (x : Pushout f g)
             → d-pre n (λ x → h x +[ n ]ₖ l x) x ≡ d-pre n h x +[ suc n ]ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (rUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (inr x) = sym (lUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (push a i) j =
    hcomp (λ k → λ { (i = i0) → rUnitₖ (suc n) (0ₖ (suc n)) (~ j)
                    ; (i = i1) → lUnitₖ (suc n) (0ₖ (suc n)) (~ j)
                    ; (j = i0) → Kn→ΩKn+1-hom n (h a) (l a) (~ k) i
                    ; (j = i1) → cong₂Funct (λ x y → x +[ (suc n) ]ₖ y) (Kn→ΩKn+1 n (h a)) (Kn→ΩKn+1 n (l a)) (~ k) i })
          (hcomp (λ k → λ { (i = i0) → rUnitₖ (suc n) (0ₖ (suc n)) (~ j)
                           ; (i = i1) → lUnitₖ (suc n) (Kn→ΩKn+1 n (l a) k) (~ j)})
                 (hcomp (λ k → λ { (i = i0) → rUnitₖ (suc n) (0ₖ (suc n)) (~ j)
                                  ; (i = i1) → lUnitₖ≡rUnitₖ (suc n) (~ k) (~ j)
                                  ; (j = i0) → Kn→ΩKn+1 n (h a) i
                                  ; (j = i1) → (Kn→ΩKn+1 n (h a) i) +[ (suc n) ]ₖ coHom-pt (suc n)})
                        (rUnitₖ (suc n) (Kn→ΩKn+1 n (h a) i) (~ j))))

  dIsHom : (n : ℕ) → isGroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂)
  dIsHom n = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                     λ f g i → ∣ funExt (λ x → dHomHelper n f g x) i ∣₂

  d : (n : ℕ) → GroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g))
  GroupHom.fun (d n) = sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂
  GroupHom.isHom (d n) = dIsHom n

  -- The long exact sequence
  Im-d⊂Ker-i : (n : ℕ) (x : ⟨ (coHomGr (suc n) (Pushout f g)) ⟩)
            → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
            → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
  Im-d⊂Ker-i n = sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
                       λ a → pRec (isOfHLevelPath' 1 (isSet× setTruncIsSet setTruncIsSet) _ _)
                               (sigmaElim (λ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
                                λ δ b i → sRec (isSet× setTruncIsSet setTruncIsSet)
                                               (λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂ ) (b (~ i)))


  Ker-i⊂Im-d : (n : ℕ) (x : ⟨ coHomGr (suc n) (Pushout f g) ⟩)
             → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
             → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
  Ker-i⊂Im-d n =
     sElim (λ _ → isSetΠ λ _ → isProp→isSet propTruncIsProp)
           λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → 0ₖ (suc n)}
                        (isProp→ propTruncIsProp)
                        (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn n (sym (cong (λ F → F (f c)) p1)
                                                                                     ∙∙ cong a (push c)
                                                                                     ∙∙ cong (λ F → F (g c)) p2)) ∣₂
                                                                             , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
                                       (Iso.fun PathIdTrunc₀Iso (cong fst p))
                                       (Iso.fun PathIdTrunc₀Iso (cong snd p))

      where
      helper : (F : (Pushout f g) → coHomK (suc n))
               (p1 : Path (_ → coHomK (suc n)) (λ a₁ → F (inl a₁)) (λ _ → coHom-pt (suc n)))
               (p2 : Path (_ → coHomK (suc n)) (λ a₁ → F (inr a₁)) (λ _ → coHom-pt (suc n)))
             → (δ : Pushout f g)
             → d-pre n (λ c → ΩKn+1→Kn n ((λ i₁ → p1 (~ i₁) (f c))
                                                     ∙∙ cong F (push c)
                                                     ∙∙ cong (λ F → F (g c)) p2)) δ
              ≡ F δ
      helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
      helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
      helper F p1 p2 (push a i) j =
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                       ; (i = i1) → p2 (~ j) (g a)
                       ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 n) ((λ i₁ → p1 (~ i₁) (f a))
                                                                       ∙∙ cong F (push a)
                                                                       ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
                        ; (j = i1) → F (push a i)})
              (doubleCompPath-filler (sym (cong (λ F → F (f a)) p1)) (cong F (push a)) (cong (λ F → F (g a)) p2) (~ j) i)

  open GroupHom

  Im-i⊂Ker-Δ : (n : ℕ) (x : ⟨ ×coHomGr n A B ⟩)
            → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) x
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) x
  Im-i⊂Ker-Δ n (Fa , Fb) =
    sElim {B = λ Fa → (Fb : _) → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) (Fa , Fb)
                               → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) (Fa , Fb)}
          (λ _ → isSetΠ2 λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          (λ Fa → sElim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                        λ Fb → pRec (setTruncIsSet _ _)
                                     (sigmaElim (λ x → isProp→isSet (setTruncIsSet _ _))
                                                λ Fd p → helper n Fa Fb Fd p))
          Fa
          Fb
    where
    helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n) (Fd : (Pushout f g) → coHomK n)
          → (fun (i n) ∣ Fd ∣₂ ≡ (∣ Fa ∣₂ , ∣ Fb ∣₂))
          → (fun (Δ n)) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
    helper n Fa Fb Fd p = cong (fun (Δ n)) (sym p)
                           ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ n ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂ )
                           ∙∙ rCancelₕ n ∣ (λ x → Fd (inl (f x))) ∣₂

  Ker-Δ⊂Im-i : (n : ℕ) (a : ⟨ ×coHomGr n A B ⟩)
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) a
            → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) a
  Ker-Δ⊂Im-i n = prodElim (λ _ → isSetΠ (λ _ → isProp→isSet propTruncIsProp))
                          (λ Fa Fb p → pRec propTruncIsProp
                                            (λ q → ∣ ∣ helpFun Fa Fb q ∣₂ , refl ∣₁)
                                            (helper Fa Fb p))
    where
    helper : (Fa : A → coHomK n) (Fb : B → coHomK n)
           → fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
           → ∥ Path (_ → _) (λ c → Fa (f c)) (λ c → Fb (g c)) ∥₁
    helper Fa Fb p = Iso.fun PathIdTrunc₀Iso
                               (sym (cong ∣_∣₂ (funExt (λ x → sym (assocₖ n _ _ _)
                               ∙∙ cong (λ y → Fa (f x) +[ n ]ₖ y) (lCancelₖ n (Fb (g x)))
                               ∙∙ rUnitₖ n (Fa (f x)))))
                               ∙∙ cong (λ x → x +[ n ]ₕ ∣ (λ c → Fb (g c)) ∣₂) p
                               ∙∙ lUnitₕ n _)

    helpFun : (Fa : A → coHomK n) (Fb : B → coHomK n)
            → ((λ c → Fa (f c)) ≡ (λ c → Fb (g c)))
            → Pushout f g → coHomK n
    helpFun Fa Fb p (inl x) = Fa x
    helpFun Fa Fb p (inr x) = Fb x
    helpFun Fa Fb p (push a i) = p i a

  private
    distrHelper : (n : ℕ) (p q : _)
                → ΩKn+1→Kn n p +[ n ]ₖ (-[ n ]ₖ ΩKn+1→Kn n q) ≡ ΩKn+1→Kn n (p ∙ sym q)
    distrHelper n p q = cong (λ x → ΩKn+1→Kn n p +[ n ]ₖ x) helper ∙ sym (ΩKn+1→Kn-hom n _ _)
      where
      helper : -[ n ]ₖ ΩKn+1→Kn n q ≡ ΩKn+1→Kn n (sym q)
      helper =
           sym (rUnitₖ n _)
        ∙∙ cong (λ x → (-[ n ]ₖ (ΩKn+1→Kn n q)) +[ n ]ₖ x) (sym helper2)
        ∙∙ (assocₖ n _ _ _ ∙∙ cong (λ x → x +[ n ]ₖ (ΩKn+1→Kn n (sym q))) (lCancelₖ n _) ∙∙ lUnitₖ n _)
        where
        helper2 : ΩKn+1→Kn n q +[ n ]ₖ (ΩKn+1→Kn n (sym q)) ≡ coHom-pt n
        helper2 = sym (ΩKn+1→Kn-hom n q (sym q)) ∙∙ cong (ΩKn+1→Kn n) (rCancel q) ∙∙ ΩKn+1→Kn-refl n

  Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n C)
             → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  Ker-d⊂Im-Δ n =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn n (cong (λ f → f (inl a)) p)) ∣₂ ,
                                                     ∣ (λ b → ΩKn+1→Kn n (cong (λ f → f (inr b)) p)) ∣₂) ,
                                                  Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 Fc p c) ∣₁ ∣₁)
                                         (Iso.fun (PathIdTrunc₀Iso) p)

    where

    helper2 : (Fc : C → coHomK n)
              (p : d-pre n Fc ≡ (λ _ → coHom-pt (suc n))) (c : C)
            → ΩKn+1→Kn n (λ i₁ → p i₁ (inl (f c))) -[ n ]ₖ (ΩKn+1→Kn n (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
    helper2 Fc p c = distrHelper n _ _ ∙∙ cong (ΩKn+1→Kn n) helper3 ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 n) (Fc c)
      where
      helper3 : (λ i₁ → p i₁ (inl (f c))) ∙ sym (λ i₁ → p i₁ (inr (g c))) ≡ Kn→ΩKn+1 n (Fc c)
      helper3 = cong ((λ i₁ → p i₁ (inl (f c))) ∙_) (lUnit _) ∙ sym (PathP→compPathR (cong (λ f → cong f (push c)) p))

  Im-Δ⊂Ker-d : (n : ℕ) (a : coHom n C)
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
             → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
  Im-Δ⊂Ker-d n =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ Fc → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
                       (sigmaProdElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                                      λ Fa Fb p → pRec (isOfHLevelPath' 1 setTruncIsSet _ _)
                                                        (λ q → ((λ i → fun (d n) ∣ (q (~ i)) ∣₂) ∙ dΔ-Id n Fa Fb))
                                                        (Iso.fun (PathIdTrunc₀Iso) p))

    where
    d-preLeftId : (n : ℕ) (Fa : A → coHomK n)(d : (Pushout f g))
                → d-pre n (Fa ∘ f) d ≡ 0ₖ (suc n)
    d-preLeftId n Fa (inl x) = Kn→ΩKn+1 n (Fa x)
    d-preLeftId n Fa (inr x) = refl
    d-preLeftId n Fa (push a i) j = Kn→ΩKn+1 n (Fa (f a)) (j ∨ i)

    d-preRightId : (n : ℕ) (Fb : B → coHomK n) (d : (Pushout f g))
                → d-pre n (Fb ∘ g) d ≡ 0ₖ (suc n)
    d-preRightId n Fb (inl x) = refl
    d-preRightId n Fb (inr x) = sym (Kn→ΩKn+1 n (Fb x))
    d-preRightId n Fb (push a i) j = Kn→ΩKn+1 n (Fb (g a)) (~ j ∧ i)

    dΔ-Id : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
            → fun (d n) (fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂)) ≡ 0ₕ (suc n)
    dΔ-Id n Fa Fb = -distrLemma n (suc n) (d n) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
                    ∙∙ (λ i → ∣ (λ x → d-preLeftId n Fa x i) ∣₂ -[ (suc n) ]ₕ ∣ (λ x → d-preRightId n Fb x i) ∣₂)
                    ∙∙ rCancelₕ (suc n) (0ₕ (suc n))
