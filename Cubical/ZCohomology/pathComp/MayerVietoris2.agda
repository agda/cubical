{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.pathComp.MayerVietoris2 where

open import Cubical.ZCohomology.pathComp.Base hiding (coHom) renaming (coHom' to coHom)
open import Cubical.ZCohomology.pathComp.Properties2
open import Cubical.ZCohomology.pathComp.EilenbergIso

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
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
open import Cubical.Data.Prod hiding (_×_)
open import Cubical.Algebra.Group
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)

open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Equiv.HalfAdjoint

open GroupHom

wrapItUp : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y) → y ≡ y
wrapItUp p q = sym q ∙∙ p ∙∙ q

wrapInv : ∀ {ℓ} {A : Type ℓ} {x y : A} → (p : x ≡ x) → (q : x ≡ y) → wrapItUp (wrapItUp p q) (sym q) ≡ p
wrapInv p q = (λ i → (λ j → q (~ i ∧ j)) ∙∙ (λ j → q (~ i ∧ ~ j))
                    ∙∙ p
                    ∙∙ (λ j → q (~ i ∧ j)) ∙∙ λ j → q (~ i ∧ ~ j))
             ∙ λ i → rUnit (rUnit p (~ i)) (~ i)

wrapFunct : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ x) (r : x ≡ y)
            → wrapItUp (p ∙ q) r ≡ wrapItUp p r ∙ wrapItUp q r
wrapFunct p q r =
    doubleCompPath-elim' (sym r) (p ∙ q) r
 ∙∙ cong (sym r ∙_) (sym (assoc p q r))
 ∙∙ assoc (sym r) p (q ∙ r)
 ∙∙ cong (_∙ (q ∙ r)) (leftright (sym r) p)
 ∙∙ λ i → (sym r ∙∙ p ∙∙ λ j → r (i ∧ j)) ∙ ((λ j → r (i ∧ ~ j)) ∙∙ q ∙∙ r)

wrapRefl : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → wrapItUp refl p ≡ refl
wrapRefl p = (λ i → (λ j → p (i ∨ ~ j)) ∙∙ refl ∙∙ λ j → p (i ∨ j)) ∙ sym (rUnit refl)

wrapItUpIso : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) → Iso (x ≡ x) (y ≡ y)
Iso.fun (wrapItUpIso p) q = wrapItUp q p
Iso.inv (wrapItUpIso p) q = wrapItUp q (sym p)
Iso.rightInv (wrapItUpIso p) q = wrapInv q (sym p)
Iso.leftInv (wrapItUpIso p) q = wrapInv q p

module MV {ℓ ℓ' ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') (f : C → A) (g : C → B) where
  -- Proof from Brunerie 2016.
  -- We first define the three morphisms involved: i, Δ and d.

  private
    i* : (n : ℕ) → coHom n (Pushout f g) → coHom n A × coHom n B
    i* _ = sRec (isSet× setTruncIsSet setTruncIsSet) λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂

  iIsHom : (n : ℕ) → isGroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B) (i* n)
  iIsHom _ = sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _) λ _ _ → refl

  i : (n : ℕ) → GroupHom (coHomGr n (Pushout f g)) (×coHomGr n A B)
  GroupHom.fun (i n) = i* n
  GroupHom.isHom (i n) = iIsHom n

  private
    distrLem : (n : ℕ) (x y z w : loopK n) → (x ∙ y) ∙ sym (z ∙ w) ≡ (x ∙ sym z) ∙ (y ∙ sym w)
    distrLem n x y z w =
      (cong ((x ∙ y) ∙_) (-distrₖ n z w))
      ∙∙ sym (assoc x y (sym z ∙ sym w)) 
      ∙∙ cong (x ∙_) (assoc y (sym z) (sym w))
      ∙∙ cong (λ s → x ∙ s ∙ sym w) (commₖ n y (sym z))
      ∙∙ (cong (x ∙_) (sym (assoc (sym z) y (sym w)))
       ∙ assoc x (sym z) (y ∙ sym w))

    Δ' : (n : ℕ) → ⟨ ×coHomGr n A B ⟩ → ⟨ coHomGr n C ⟩
    Δ' n (α , β) = coHomFun n f α -[ n ]ₕ coHomFun n g β

    Δ'-isMorph : (n : ℕ) → isGroupHom (×coHomGr n A B) (coHomGr n C) (Δ' n)
    Δ'-isMorph n =
      prodElim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _ )
        λ f' x1 g' x2 → cong ∣_∣₂ (funExt λ x → distrLem n (f' (f x)) (g' (f x)) (x1 (g x)) (x2 (g x)))

  Δ : (n : ℕ) → GroupHom (×coHomGr n A B) (coHomGr n C)
  GroupHom.fun (Δ n) = Δ' n
  GroupHom.isHom (Δ n) = Δ'-isMorph n

  d-pathIso : (n : ℕ) → Iso (loopK n) (Path (loopK (suc n)) (0ₖ (suc n)) (0ₖ (suc n)))
  d-pathIso n = compIso (congIso (Iso-Kn-ΩKn+1 (suc n))) (wrapItUpIso (Kn-ΩKn+10→0 n))

  d-path : (n : ℕ) → loopK n → Path (loopK (suc n)) (0ₖ (suc n)) (0ₖ (suc n))
  d-path n = Iso.fun (d-pathIso n)

  d-path0 : (n : ℕ) → d-path n refl ≡ refl
  d-path0 n = wrapRefl _

  d-path⁻ : (n : ℕ) → Path (loopK (suc n)) (0ₖ (suc n)) (0ₖ (suc n)) → loopK n
  d-path⁻ n = Iso.inv (d-pathIso n)

  d-path-funct : (n : ℕ) → (x y : loopK n) → d-path n (x ∙ y) ≡ d-path n x ∙ d-path n y
  d-path-funct n x y = cong (λ x → wrapItUp x (Kn-ΩKn+10→0 n)) (congFunct (Iso.fun (Iso-Kn-ΩKn+1 (suc n))) x y)
                          ∙ wrapFunct (cong (Iso.fun (Iso-Kn-ΩKn+1 (suc n))) x) (cong (Iso.fun (Iso-Kn-ΩKn+1 (suc n))) y) (Kn-ΩKn+10→0 n)

  d-path⁻-funct : (n : ℕ) → (p q : Path (loopK (suc n)) (0ₖ (suc n)) (0ₖ (suc n)))
               → d-path⁻ n (p ∙ q) ≡ d-path⁻ n p ∙ d-path⁻ n q
  d-path⁻-funct n p q = cong (Iso.inv (congIso (Iso-Kn-ΩKn+1 (suc n)))) (wrapFunct p q (sym (Kn-ΩKn+10→0 n)))
                     ∙ invCongFunct (Iso-Kn-ΩKn+1 (suc n)) _ _

  d-path⁻0 : (n : ℕ) → d-path⁻ n refl ≡ refl
  d-path⁻0 n = cong (Iso.inv (congIso (Iso-Kn-ΩKn+1 (suc n)))) (wrapRefl _)
             ∙ invCongRefl (Iso-Kn-ΩKn+1 (suc n))

  d-path⁻-minus : (n : ℕ) → (p : Path (loopK (suc n)) (0ₖ (suc n)) (0ₖ (suc n))) → d-path⁻ n (sym p) ≡ sym (d-path⁻ n p)
  d-path⁻-minus n p =
       rUnit _
    ∙∙ cong (d-path⁻ n (sym p) ∙_) (sym (rCancel (d-path⁻ n p)))
    ∙∙ assoc _ _ _
    ∙∙ cong (_∙ sym (d-path⁻ n p)) help
    ∙∙ sym (lUnit _)
    where
    help : d-path⁻ n (sym p) ∙ d-path⁻ n p ≡ refl
    help = sym (d-path⁻-funct n _ _)
        ∙∙ cong (d-path⁻ n) (lCancel p)
        ∙∙ d-path⁻0 n

  d-path⁻-Minusfunct : (n : ℕ) → (p q : Path (loopK (1 + n)) refl refl)
               → d-path⁻ n (p ∙ (sym q)) ≡ d-path⁻ n p ∙ d-path⁻ n (sym q)
  d-path⁻-Minusfunct n p q = d-path⁻-funct n p (sym q)
                          ∙ cong (d-path⁻ n p ∙_) (d-path⁻-minus n q)

  d-pre : (n : ℕ) → (C → loopK n) → Pushout f g → loopK (suc n)
  d-pre n γ (inl x) = 0ₖ (suc n)
  d-pre n γ (inr x) = 0ₖ (suc n)
  d-pre n γ (push a i) = d-path n (γ a) i

  dHomHelper : (n : ℕ) (h l : C → loopK n) (x : Pushout f g)
             → d-pre n (λ x → h x ∙ l x) x ≡ d-pre n h x ∙ d-pre n l x
  dHomHelper n h l (inl x) = rUnit _
  dHomHelper n h l (inr x) = lUnit _
  dHomHelper n h l (push a i) j = helpi (h a) (l a) j i
    where
    helpi : (x y : loopK n) → PathP (λ j → rUnit (0ₖ (suc n)) j ≡ lUnit (0ₖ (suc n)) j)
                                     (d-path n (x ∙ y))
                                     (cong₂ (_∙_) (d-path n x) (d-path n y))
    helpi x y i j =
      hcomp (λ k → λ { (i = i0) → d-path-funct n x y (~ k) j
                      ; (i = i1) → cong₂Funct (_∙_) (d-path n x) (d-path n y) (~ k) j
                      ; (j = i0) → rUnit (0ₖ (suc n)) i
                      ; (j = i1) → lUnit (0ₖ (suc n)) i})
            (hcomp (λ k → λ { (j = i0) → rUnit (0ₖ (suc n)) i
                             ; (j = i1) → lUnit (d-path n y k) i })
                   (rUnit (d-path n x j) i))

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
           λ a p → pRec {A = (λ x → a (inl x)) ≡ λ _ → 0ₖ (suc n)} (isProp→ propTruncIsProp)
                        (λ p1 → pRec propTruncIsProp λ p2 → ∣ ∣ (λ c → d-path⁻ n (sym (cong (λ F → F (f c)) p1)
                                                                                           ∙∙ cong a (push c)
                                                                                           ∙∙ cong (λ F → F (g c)) p2)) ∣₂
                                                                             , cong ∣_∣₂ (funExt (λ δ → helper a p1 p2 δ)) ∣₁)
                                       (Iso.fun PathIdTrunc₀Iso (cong fst p))
                                       (Iso.fun PathIdTrunc₀Iso (cong snd p))

      where
      helper : (F : (Pushout f g) → loopK (suc n))
               (p1 : Path (_ → loopK (suc n)) (λ a₁ → F (inl a₁)) (λ _ → refl))
               (p2 : Path (_ → loopK (suc n)) (λ a₁ → F (inr a₁)) (λ _ → refl))
             → (δ : (Pushout f g))
             → d-pre n (λ c → d-path⁻ n ((λ i₁ → p1 (~ i₁) (f c))
                                                     ∙∙ cong F (push c)
                                                     ∙∙ cong (λ F → F (g c)) p2)) δ
              ≡ F δ
      helper F p1 p2 (inl x) = sym (cong (λ f → f x) p1)
      helper F p1 p2 (inr x) = sym (cong (λ f → f x) p2)
      helper F p1 p2 (push a i) j =
        hcomp (λ k → λ { (i = i0) → p1 (~ j) (f a)
                       ; (i = i1) → p2 (~ j) (g a)
                       ; (j = i0) → Iso.rightInv (d-pathIso n) ((λ i₁ → p1 (~ i₁) (f a))
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
    helper : (n : ℕ) (Fa : A → loopK n) (Fb : B → loopK n) (Fd : (Pushout f g) → loopK n)
          → (fun (i n) ∣ Fd ∣₂ ≡ (∣ Fa ∣₂ , ∣ Fb ∣₂))
          → (fun (Δ n)) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
    helper n Fa Fb Fd p = cong (fun (Δ n)) (sym p)
                              ∙∙ (λ i → ∣ (λ x → Fd (inl (f x))) ∣₂ -[ n ]ₕ ∣ (λ x → Fd (push x (~ i))) ∣₂)
                              ∙∙ rCancelₕ n ∣ (λ x → Fd (inl (f x))) ∣₂

  Ker-Δ⊂Im-i : (n : ℕ) (a : ⟨ ×coHomGr n A B ⟩)
            → isInKer (×coHomGr n A B) (coHomGr n C) (Δ n) a
            → isInIm (coHomGr n (Pushout f g)) (×coHomGr n A B) (i n) a
  Ker-Δ⊂Im-i n = prodElim (λ _ → isSetΠ (λ _ → isProp→isSet propTruncIsProp))
                          (λ Fa Fb p → pRec propTruncIsProp
                                            (λ q → ∣ ∣ helpFun Fa Fb q ∣₂ , refl ∣₁)
                                            (helper Fa Fb p))
    where
    helper : (Fa : A → loopK n) (Fb : B → loopK n)
           → fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂) ≡ 0ₕ n
           → ∥ Path (_ → _) (λ c → Fa (f c)) (λ c → Fb (g c)) ∥₁
    helper Fa Fb p =
      Iso.fun PathIdTrunc₀Iso (sym (cong ∣_∣₂ (funExt λ x → cancel-lem _ _))
                               ∙∙ cong (λ x → x +[ n ]ₕ ∣ (λ c → Fb (g c)) ∣₂) p
                               ∙∙ lUnitₕ n _)
      where
      cancel-lem : (x y : loopK n) → (x ∙ sym y) ∙ y ≡ x
      cancel-lem x y = sym (assoc x (sym y) y) ∙∙ cong (x ∙_) (lCancel y) ∙∙ sym (rUnit x)

    helpFun : (Fa : A → loopK n) (Fb : B → loopK n)
            → ((λ c → Fa (f c)) ≡ (λ c → Fb (g c)))
            → Pushout f g → loopK n
    helpFun Fa Fb p (inl x) = Fa x
    helpFun Fa Fb p (inr x) = Fb x
    helpFun Fa Fb p (push a i) = p i a

  Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n C)
             → isInKer (coHomGr n C) (coHomGr (suc n) (Pushout f g)) (d n) a
             → isInIm (×coHomGr n A B) (coHomGr n C) (Δ n) a
  Ker-d⊂Im-Δ n =
    sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ Fc p → pRec propTruncIsProp (λ p → ∣ (∣ (λ a → d-path⁻ n (funExt⁻ p (inl a))) ∣₂ , ∣ (λ a → d-path⁻ n (funExt⁻ p (inr a))) ∣₂) ,
                                                  cong ∣_∣₂ (funExt (λ c → helper2 Fc p c)) ∣₁)
                                         (Iso.fun (PathIdTrunc₀Iso) p)

    where
    helper2 : (Fc : C → loopK n)
              (p : d-pre n Fc ≡ (λ _ → refl)) (c : C)
            → d-path⁻ n (λ i₁ → p i₁ (inl (f c))) ∙ sym (d-path⁻ n (λ i₁ → p i₁ (inr (g c)))) ≡ Fc c
    helper2 Fc p c = sym (d-path⁻-Minusfunct n (λ i₁ → p i₁ (inl (f c))) (λ i₁ → p i₁ (inr (g c))))
                          ∙∙ cong (d-path⁻ n) (sym (rUnit _
                                                 ∙∙ cong (d-path n (Fc c) ∙_) (sym (rCancel (funExt⁻ p (inr (g c)))))
                                                 ∙∙ assoc _ _ _
                                                 ∙ cong (λ x → x ∙ (sym (funExt⁻ p (inr (g c)))))
                                                   (cong (d-path n (Fc c) ∙_) (rUnit (funExt⁻ p (inr (g c))))
                                                 ∙ sym (PathP→compPathR (cong (funExt⁻ p) (push c))))))
                          ∙∙ Iso.leftInv (d-pathIso n) (Fc c)

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
    d-preLeftId : (n : ℕ) (Fa : A → loopK n)(d : (Pushout f g))
                → d-pre n (Fa ∘ f) d ≡ 0ₖ (suc n)
    d-preLeftId n Fa (inl x) = d-path n (Fa x)
    d-preLeftId n Fa (inr x) = refl
    d-preLeftId n Fa (push a i) j = d-path n (Fa (f a)) (j ∨ i)

    d-preRightId : (n : ℕ) (Fb : B → loopK n) (d : (Pushout f g))
                → d-pre n (Fb ∘ g) d ≡ 0ₖ (suc n)
    d-preRightId n Fb (inl x) = refl
    d-preRightId n Fb (inr x) = sym (d-path n (Fb x))
    d-preRightId n Fb (push a i) j = d-path n (Fb (g a)) (~ j ∧ i)

    dΔ-Id : (n : ℕ) (Fa : A → loopK n) (Fb : B → loopK n)
            → fun (d n) (fun (Δ n) (∣ Fa ∣₂ , ∣ Fb ∣₂)) ≡ 0ₕ (suc n)
    dΔ-Id n Fa Fb = -distrLemma n (suc n) (d n) ∣ Fa ∘ f ∣₂ ∣ Fb ∘ g ∣₂
                  ∙∙ (λ i → ∣ (λ x → d-preLeftId n Fa x i) ∣₂ -[ (suc n) ]ₕ ∣ (λ x → d-preRightId n Fb x i) ∣₂)
                  ∙∙ rCancelₕ (suc n) (0ₕ (suc n))
