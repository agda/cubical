{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.MayerVietorisUnreduced where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.KcompPrelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.Data.Prod hiding (_×_)
open import Cubical.HITs.Truncation.FromNegOne renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)
open import Cubical.Algebra.Group

open GroupHom

module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  -- Proof from Brunerie 2016.
  -- We first define the three morphisms involved: i, Δ and d.

  private
    i* : (n : ℕ) → coHom n (Pushout f g) → coHom n A × coHom n B
    i* zero = sRec (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet))
                    λ δ →  ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂
    i* (suc n) = sRec (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet))
                      λ δ →  ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂

  iIsHom : (n : ℕ) → isGroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B) (i* n)
  iIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                         λ f g → refl
  iIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                         λ f g → refl

  i : (n : ℕ) → GroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B)
  GroupHom.fun (i n) = i* n
  GroupHom.isHom (i n) = iIsHom n


  private
    distrLem : (n : ℕ) (x y z w : coHomK n) → (x +[ n ]ₖ y) -[ n ]ₖ (z +[ n ]ₖ w) ≡ (x -[ n ]ₖ z) +[ n ]ₖ (y -[ n ]ₖ w)
    distrLem n x y z w =
         cong (ΩKn+1→Kn n) (cong₂ (λ q p → q ∙ sym p) (+ₖ→∙ n x y) (+ₖ→∙ n z w)
                        ∙∙ cong ((Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y) ∙_) (symDistr (Kn→ΩKn+1 n z) (Kn→ΩKn+1 n w))
                        ∙∙ ((sym (assoc (Kn→ΩKn+1 n x) (Kn→ΩKn+1 n y) _))
                        ∙∙ cong (Kn→ΩKn+1 n x ∙_) (assoc (Kn→ΩKn+1 n y) (sym (Kn→ΩKn+1 n w)) (sym (Kn→ΩKn+1 n z)))
                        ∙∙ (cong (Kn→ΩKn+1 n x ∙_) (isCommΩK (suc n) _ _)
                        ∙∙ assoc _ _ _
                        ∙∙ cong₂ _∙_ (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n x ∙ sym (Kn→ΩKn+1 n z))))
                                     (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) (Kn→ΩKn+1 n y ∙ sym (Kn→ΩKn+1 n w)))))))


    Δ' : (n : ℕ) → ⟨ ×coHomGr n A B ⟩ → ⟨ coHomGr n C ⟩
    Δ' n (α , β) = (coHomFun n f α) -[ n ]ₕ (coHomFun n g β)
    Δ'-isMorph : (n : ℕ) → isGroupHom (×coHomGr n A B) (coHomGr n C) (Δ' n)
    Δ'-isMorph zero =
      prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
        λ f' x1 g' x2 i → ∣ (λ x → distrLem 0 (f' (f x)) (g' (f x)) (x1 (g x)) (x2 (g x)) i) ∣₂
    Δ'-isMorph (suc n) =
      prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
        λ f' x1 g' x2 i → ∣ (λ x → distrLem (suc n) (f' (f x)) (g' (f x)) (x1 (g x)) (x2 (g x)) i) ∣₂

  Δ : (n : ℕ) → GroupHom (×coHomGr n A B) (coHomGr n C)
  GroupHom.fun (Δ n) = Δ' n
  GroupHom.isHom (Δ n) = Δ'-isMorph n

  d-pre : (n : ℕ) → (C → coHomK n) → (Pushout f g) → coHomK (suc n)
  d-pre n γ (inl x) = 0ₖ (suc n)
  d-pre n γ (inr x) = 0ₖ (suc n)
  d-pre zero γ (push a i) = Kn→ΩKn+1 zero (γ a) i
  d-pre (suc n) γ (push a i) = Kn→ΩKn+1 (suc n) (γ a) i

  dHomHelperPath : (n : ℕ) (h l : C → coHomK n) (a : C) → I → I → coHomK (suc n)
  dHomHelperPath zero h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ 1 (0ₖ 1) (~ j)
                   ; (i = i1) → lUnitₖ 1 (0ₖ 1) (~ j)
                   ; (j = i0) → +ₖ→∙ 0 (h a) (l a) (~ k) i
                   ; (j = i1) → cong₂Funct (λ x y → x +[ 1 ]ₖ y)
                                           (Kn→ΩKn+1 0 (h a)) (Kn→ΩKn+1 0 (l a)) (~ k) i})
          (bottom i j)
       where
       bottom : I → I → coHomK 1
       bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ 1 (0ₖ 1) (~ j)
                                   ; (i = i1) → lUnitₖ 1 (Kn→ΩKn+1 0 (l a) k) (~ j) })
                          (anotherbottom i j)

         where
         anotherbottom : I → I → coHomK 1
         anotherbottom i j =  hcomp (λ k → λ { (i = i0) → rUnitlUnit0 1 k (~ j)
                                             ; (i = i1) → rUnitlUnit0 1 k (~ j)
                                             ; (j = i0) → Kn→ΩKn+1 0 (h a) i
                                             ; (j = i1) → Kn→ΩKn+1 0 (h a) i +[ 1 ]ₖ 0ₖ 1 })
                                    (rUnitₖ 1 (Kn→ΩKn+1 0 (h a) i) (~ j))
  dHomHelperPath (suc n) h l a i j =
    hcomp (λ k → λ { (i = i0) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                   ; (i = i1) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                   ; (j = i0) → +ₖ→∙ (suc n) (h a) (l a) (~ k) i
                   ; (j = i1) → cong₂Funct (λ x y → x +[ 2 + n ]ₖ y)
                                           (Kn→ΩKn+1 (suc n) (h a)) (Kn→ΩKn+1 (suc n) (l a)) (~ k) i})
          (bottom i j)
      where
      bottom : I → I → coHomK (2 + n)
      bottom i j = hcomp (λ k → λ { (i = i0) → lUnitₖ (2 + n) (0ₖ (2 + n)) (~ j)
                                  ; (i = i1) → lUnitₖ (2 + n) (Kn→ΩKn+1 (suc n) (l a) k) (~ j) })
                         (anotherbottom i j)

        where
        anotherbottom : I → I → coHomK (2 + n)
        anotherbottom i j = hcomp (λ k → λ { (i = i0) → rUnitlUnit0 (2 + n) k (~ j)
                                           ; (i = i1) → rUnitlUnit0 (2 + n) k (~ j)
                                           ; (j = i0) → Kn→ΩKn+1 (suc n) (h a) i
                                           ; (j = i1) → Kn→ΩKn+1 (suc n) (h a) i +[ 2 + n ]ₖ (0ₖ (2 + n)) })
                                  (rUnitₖ (2 + n) (Kn→ΩKn+1 (suc n) (h a) i) (~ j))

  dHomHelper : (n : ℕ) (h l : C → coHomK n) (x : Pushout f g)
             → d-pre n (λ x → h x +[ n ]ₖ l x) x ≡ d-pre n h x +[ suc n ]ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (lUnitₖ (suc n) (0ₖ (suc n))) -- sym (suc n) (lUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (inr x) = sym (lUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper zero h l (push a i) j = dHomHelperPath zero h l a i j
  dHomHelper (suc n) h l (push a i) j = dHomHelperPath (suc n) h l a i j

  dIsHom : (n : ℕ) → isGroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂)
  dIsHom zero = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper zero f g x) i ∣₂
  dIsHom (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                   λ f g i → ∣ funExt (λ x → dHomHelper (suc n) f g x) i ∣₂

  d : (n : ℕ) → GroupHom (coHomGr n C) (coHomGr (suc n) (Pushout f g))
  GroupHom.fun (d n) = sRec setTruncIsSet λ a → ∣ d-pre n a ∣₂
  GroupHom.isHom (d n) = dIsHom n


  -- The long exact sequence
  Im-d⊂Ker-i : (n : ℕ) (x : ⟨ (coHomGr (suc n) (Pushout f g)) ⟩)
            → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
            → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
  Im-d⊂Ker-i n = sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                       λ a → pElim (λ _ → isOfHLevelPath' 1 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                               (sigmaElim (λ _ → isOfHLevelPath 2 (isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet)) _ _)
                                λ δ b → (λ i → sElim (λ _ → isOfHLevelΣ 2 setTruncIsSet (λ _ → setTruncIsSet))
                                                 (λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂ ) (b (~ i))))

  Ker-i⊂Im-d : (n : ℕ) (x : ⟨ coHomGr (suc n) (Pushout f g) ⟩)
              → isInKer (coHomGr (suc n) (Pushout f g)) (×coHomGr (suc n) A B) (i (suc n)) x
              → isInIm (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) x
  Ker-i⊂Im-d zero =
     sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                         λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → (0ₖ (suc 0))} (isOfHLevelΠ 1 (λ _ → propTruncIsProp))
                                       (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn 0 (sym (cong (λ F → F (f c)) p1)
                                                                                                 ∙∙ cong a (push c)
                                                                                                 ∙∙ cong (λ F → F (g c)) p2)) ∣₂
                                                                             , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
                                       (Iso.fun (PathIdTrunc₀Iso) (cong fst p))
                                       (Iso.fun (PathIdTrunc₀Iso) (cong snd p))

      where
      helper : (F : (Pushout f g) → hLevelTrunc 3 (S₊ 1))
               (p1 : Path (_ → hLevelTrunc 3 (S₊ 1)) (λ a₁ → F (inl a₁)) (λ _ → ∣ base ∣))
               (p2 : Path (_ → hLevelTrunc 3 (S₊ 1)) (λ a₁ → F (inr a₁)) (λ _ → ∣ base ∣))
             → (δ : (Pushout f g))
             → d-pre 0 (λ c → ΩKn+1→Kn 0 ((λ i₁ → p1 (~ i₁) (f c))
                                                     ∙∙ cong F (push c)
                                                     ∙∙ cong (λ F → F (g c)) p2)) δ
              ≡ F δ
      helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
      helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
      helper F p1 p2 (push a i) j =
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                       ; (i = i1) → p2 (~ j) (g a)
                       ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 zero) ((λ i₁ → p1 (~ i₁) (f a))
                                                                       ∙∙ cong F (push a)
                                                                       ∙∙ cong (λ F₁ → F₁ (g a)) p2) (~ k) i
                        ; (j = i1) → F (push a i)})
              (doubleCompPath-filler (sym (cong (λ F → F (f a)) p1)) (cong F (push a)) (cong (λ F → F (g a)) p2) (~ j) i)
  Ker-i⊂Im-d (suc n) =
   sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                         λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → (0ₖ (2 + n))} (isOfHLevelΠ 1 (λ _ → propTruncIsProp))
                                       (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → ΩKn+1→Kn (suc n) (sym (cong (λ F → F (f c)) p1)
                                                                                                 ∙∙ cong a (push c)
                                                                                                 ∙∙ cong (λ F → F (g c)) p2)) ∣₂
                                                                             , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
                                       (Iso.fun (PathIdTrunc₀Iso) (cong fst p))
                                       (Iso.fun (PathIdTrunc₀Iso) (cong snd p))

      where
      helper : (F : (Pushout f g) → hLevelTrunc (4 + n) (S₊ (2 + n)))
               (p1 : Path (_ → hLevelTrunc (4 + n) (S₊ (2 + n))) (λ a₁ → F (inl a₁)) (λ _ → ∣ north ∣))
               (p2 : Path (_ → hLevelTrunc (4 + n) (S₊ (2 + n))) (λ a₁ → F (inr a₁)) (λ _ → ∣ north ∣))
             → (δ : (Pushout f g))
             → d-pre (suc n) (λ c → ΩKn+1→Kn (suc n) ((λ i₁ → p1 (~ i₁) (f c))
                                                     ∙∙ cong F (push c)
                                                     ∙∙ cong (λ F → F (g c)) p2)) δ
              ≡ F δ
      helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
      helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
      helper F p1 p2 (push a i) j =
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                        ; (i = i1) → p2 (~ j) (g a)
                        ; (j = i0) → Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) ((λ i₁ → p1 (~ i₁) (f a))
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
          (λ _ → isOfHLevelΠ 2 λ _ → (isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _))
          (λ Fa → sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                        λ Fb → pRec (setTruncIsSet _ _)
                                     (sigmaElim (λ x → isOfHLevelSuc 1 (setTruncIsSet _ _))
                                                λ Fd p → helper n Fa Fb Fd p))
          Fa
          Fb
    where
    helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n) (Fd : (Pushout f g) → coHomK n)
          → (fun (i n) ∣ Fd ∣₂ ≡ (∣ Fa ∣₂ , ∣ Fb ∣₂))
          → (fun (Δ n)) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
    helper zero Fa Fb Fd p = cong (fun (Δ zero)) (sym p)
                           ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ 0 ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂ ) -- (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ +[ 0 ]ₕ (-[ 0 ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂))
                           ∙∙ cancelₕ 0 ∣ (λ x → Fd (inl (f x))) ∣₂
    helper (suc n) Fa Fb Fd p = cong (fun (Δ (suc n))) (sym p)
                              ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ (suc n) ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂)
                              ∙∙ cancelₕ (suc n) ∣ (λ x → Fd (inl (f x))) ∣₂

  Ker-Δ⊂Im-i : (n : ℕ) (a : ⟨ ×coHomGr n A B ⟩)
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) a
            → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) a
  Ker-Δ⊂Im-i n (Fa , Fb) =
    sElim {B = λ Fa → (Fb : _) → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) (Fa , Fb)
                                → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) (Fa , Fb)}
          (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          (λ Fa → sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
                         λ Fb p → pRec propTruncIsProp
                                        (λ q → ∣ ∣ helpFun n Fa Fb (funExt⁻ q) ∣₂
                                                , anotherHelper n Fa Fb q ∣₁)
                                        (helper n Fa Fb p))
          Fa
          Fb

    where
    helper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
           → (fun (Δ n)) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
           → ∥  (Path (_ → _) (λ c → Fa (f c)) (λ c → Fb (g c))) ∥₁
    helper zero Fa Fb p = Iso.fun (PathIdTrunc₀Iso)
                                   (sym (-+cancelₕ 0 ∣ (λ c → Fa (f c)) ∣₂ ∣ (λ c → Fb (g c)) ∣₂)
                                 ∙∙ cong (λ x → x +[ 0 ]ₕ ∣ (λ c → Fb (g c)) ∣₂) p
                                 ∙∙ lUnitₕ 0 _)
    helper (suc n) Fa Fb p = Iso.fun (PathIdTrunc₀Iso)
                                      (sym (-+cancelₕ (suc n) ∣ (λ c → Fa (f c)) ∣₂ ∣ (λ c → Fb (g c)) ∣₂)
                                    ∙∙ cong (λ x → x +[ (suc n) ]ₕ ∣ (λ c → Fb (g c)) ∣₂) p
                                    ∙∙ lUnitₕ (suc n) _)

    helpFun : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
            → ((c : C) → Fa (f c) ≡ Fb (g c))
            → (Pushout f g) → coHomK n
    helpFun n Fa Fb p (inl x) = Fa x
    helpFun n Fa Fb p (inr x) = Fb x
    helpFun n Fa Fb p (push a i) = p a i

    anotherHelper : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
                 → (q : Path (C → coHomK n) (λ c → Fa (f c)) (λ c → Fb (g c)))
                 → fun (i n) ∣ helpFun n Fa Fb (λ x i₁ → q i₁ x) ∣₂ ≡ (∣ Fa ∣₂ , ∣ Fb ∣₂)
    anotherHelper zero Fa Fb q = refl
    anotherHelper (suc n) Fa Fb q = refl

  private
    distrHelper : (n : ℕ) (p q : _)
                → ΩKn+1→Kn n p +[ n ]ₖ (-[ n ]ₖ ΩKn+1→Kn n q) ≡ ΩKn+1→Kn n (p ∙ sym q)
    distrHelper n p q i =
        ΩKn+1→Kn n (Iso.rightInv (Iso-Kn-ΩKn+1 n) p i
      ∙ Iso.rightInv (Iso-Kn-ΩKn+1 n) (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) q i)) i)


  Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n C)
             → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  Ker-d⊂Im-Δ zero =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn 0 (cong (λ f → f (inl a)) p)) ∣₂ ,
                                                     ∣ (λ b → ΩKn+1→Kn 0 (cong (λ f → f (inr b)) p)) ∣₂) ,
                                                  Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 Fc p c) ∣₁ ∣₁)
                                         (Iso.fun (PathIdTrunc₀Iso) p)

    where

    helper2 : (Fc : C → coHomK 0)
              (p : d-pre 0 Fc ≡ (λ _ → ∣ base ∣)) (c : C)
            → ΩKn+1→Kn 0 (λ i₁ → p i₁ (inl (f c))) -[ 0 ]ₖ (ΩKn+1→Kn 0 (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
    helper2 Fc p c = cong₂ (λ x y → ΩKn+1→Kn 0 (x ∙ sym y)) (Iso.rightInv (Iso-Kn-ΩKn+1 0) (λ i₁ → p i₁ (inl (f c))))
                                                            (Iso.rightInv (Iso-Kn-ΩKn+1 0) (λ i₁ → p i₁ (inr (g c))))
                  ∙∙ cong (ΩKn+1→Kn 0) (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
                              ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
                                      ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
                  ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 zero) (Fc c)
  Ker-d⊂Im-Δ (suc n) =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → ΩKn+1→Kn (suc n) (cong (λ f → f (inl a)) p)) ∣₂ ,
                                                     ∣ (λ b → ΩKn+1→Kn (suc n) (cong (λ f → f (inr b)) p)) ∣₂) ,
                                                  Iso.inv (PathIdTrunc₀Iso) ∣ funExt (λ c → helper2 Fc p c) ∣₁ ∣₁)
                                         (Iso.fun (PathIdTrunc₀Iso) p)

    where

    helper2 : (Fc : C → coHomK (suc n))
              (p : d-pre (suc n) Fc ≡ (λ _ → ∣ north ∣)) (c : C)
            → ΩKn+1→Kn (suc n) (λ i₁ → p i₁ (inl (f c))) -[ (suc n) ]ₖ (ΩKn+1→Kn (suc n) (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
    helper2 Fc p c = cong₂ (λ x y → ΩKn+1→Kn (suc n) (x ∙ sym y)) (Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (λ i₁ → p i₁ (inl (f c))))
                                                                   (Iso.rightInv (Iso-Kn-ΩKn+1 (suc n)) (λ i₁ → p i₁ (inr (g c))))
                  ∙∙ cong (ΩKn+1→Kn (suc n)) (sym ((PathP→compPathR (cong (λ f → cong f (push c)) p))
                              ∙ (λ i → (λ i₁ → p i₁ (inl (f c)))
                                      ∙ (lUnit (sym (λ i₁ → p i₁ (inr (g c)))) (~ i)))))
                  ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (Fc c)

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
    d-preLeftId zero Fa (inl x) = Kn→ΩKn+1 0 (Fa x)
    d-preLeftId (suc n) Fa (inl x) = Kn→ΩKn+1 (suc n) (Fa x)
    d-preLeftId zero Fa (inr x) = refl
    d-preLeftId (suc n) Fa (inr x) = refl
    d-preLeftId zero Fa (push a i) j = Kn→ΩKn+1 zero (Fa (f a)) (j ∨ i)
    d-preLeftId (suc n) Fa (push a i) j = Kn→ΩKn+1 (suc n) (Fa (f a)) (j ∨ i)

    d-preRightId : (n : ℕ) (Fb : B → coHomK n) (d : (Pushout f g))
                → d-pre n (Fb ∘ g) d ≡ 0ₖ (suc n)
    d-preRightId n Fb (inl x) = refl
    d-preRightId zero Fb (inr x) = sym (Kn→ΩKn+1 0 (Fb x))
    d-preRightId (suc n) Fb (inr x) = sym (Kn→ΩKn+1 (suc n) (Fb x))
    d-preRightId zero Fb (push a i) j = Kn→ΩKn+1 zero (Fb (g a)) (~ j ∧ i)
    d-preRightId (suc n) Fb (push a i) j = Kn→ΩKn+1 (suc n) (Fb (g a)) (~ j ∧ i)

    dΔ-Id : (n : ℕ) (Fa : A → coHomK n) (Fb : B → coHomK n)
            → fun (d n) (fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂)) ≡ 0ₕ (suc n)
    dΔ-Id zero Fa Fb = -distrLemma 0 1 (d zero) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
                    ∙∙ (λ i → ∣ (λ x → d-preLeftId zero Fa x i) ∣₂ -[ 1 ]ₕ ∣ (λ x → d-preRightId zero Fb x i) ∣₂)
                    ∙∙ cancelₕ 1 (0ₕ 1)
    dΔ-Id (suc n) Fa Fb = -distrLemma (suc n) (2 + n) (d (suc n)) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
                    ∙∙ (λ i → ∣ (λ x → d-preLeftId (suc n) Fa x i) ∣₂ -[ (2 + n) ]ₕ ∣ (λ x → d-preRightId (suc n) Fb x i) ∣₂)
                    ∙∙ cancelₕ (2 + n) (0ₕ (2 + n))
