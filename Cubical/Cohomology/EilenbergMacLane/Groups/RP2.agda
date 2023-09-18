{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.RP2 where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Unit
open import Cubical.Data.Fin

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.RPn

open AbGroupStr

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module RP²Conn {B : (RP² → A) → Type ℓ} where
  elim₁ :
      isConnected 2 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → ((l1 : a* ≡ a*) (sq : l1 ≡ sym l1)
         → B (RP²Fun a* l1 sq))
    → (x : _) → B x
  elim₁  conA pr a* ind f =
    TR.rec (pr _)
      (λ p → J (λ a* _ → ((l1 : a* ≡ a*) (sq : l1 ≡ sym l1)
                        → B (RP²Fun a* l1 sq)) → B f)
                (λ ind → subst B (characRP²Fun f) (ind _ _))
                p ind)
      (isConnectedPath 1 conA (f point) a* .fst)

  elim₂ : isConnected 3 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → ((sq : refl {x = a*} ≡ refl)
         → B (RP²Fun a* refl sq))
    → (x : _) → B x
  elim₂ conA pr a* ind =
    elim₁ (isConnectedSubtr 2 1 conA)
      (λ _ → pr _)
      a*
      (λ l1 → TR.rec (isPropΠ (λ _ → pr _))
        (J (λ l1 _ → (sq : l1 ≡ sym l1) → B (RP²Fun a* l1 sq))
          ind)
        (isConnectedPath 1
          (isConnectedPath 2 conA a* a*) refl l1 .fst))

  elim₃ : isConnected 4 A
    → ((x : _) → isProp (B x))
    → (a* : A)
    → (B λ _ → a*)
    → (x : _) → B x
  elim₃ conA pr a* ind =
    elim₂ (isConnectedSubtr 3 1 conA)
      pr
      a*
      λ sq → TR.rec (pr _)
        (J (λ sq _ → B (RP²Fun a* refl sq))
          (subst B (sym (characRP²Fun (λ _ → a*))) ind))
        (isConnectedPath 1
          (isConnectedPath 2
            (isConnectedPath 3 conA _ _) _ _) refl sq .fst)


----- H¹(RP²,ℤ/2) ------
H¹[RP²,ℤ/2]→ℤ/2 : coHom 1 ℤ/2 RP² → fst ℤ/2
H¹[RP²,ℤ/2]→ℤ/2 =
  ST.rec isSetFin
    λ f → ΩEM+1→EM-gen 0 _ (cong f line)

ℤ/2→H¹[RP²,ℤ/2] : fst ℤ/2 → coHom 1 ℤ/2 RP²
ℤ/2→H¹[RP²,ℤ/2] x =
  ∣ (λ { point → embase
      ; (line i) → emloop x i
      ; (square i j) → symConst-ℤ/2 1 embase (emloop x) i j}) ∣₂

ℤ/2→H¹[RP²,ℤ/2]→ℤ/2 : (x : fst ℤ/2)
  → H¹[RP²,ℤ/2]→ℤ/2 (ℤ/2→H¹[RP²,ℤ/2] x) ≡ x
ℤ/2→H¹[RP²,ℤ/2]→ℤ/2 = Iso.leftInv (Iso-EM-ΩEM+1 0)

H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2]  : (f : coHom 1 ℤ/2 RP²)
  → ℤ/2→H¹[RP²,ℤ/2] (H¹[RP²,ℤ/2]→ℤ/2 f) ≡ f
H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2] =
  ST.elim
    (λ _ → isSetPathImplicit)
    (RP²Conn.elim₁ (isConnectedEM 1)
      (λ _ → squash₂ _ _)
      embase
      λ l sq → cong ∣_∣₂
        (funExt (elimSetRP² (λ _ → hLevelEM _ 1 _ _)
          refl
          (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l)))))

H¹[RP²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 1 ℤ/2 RP²) ℤ/2
fst H¹[RP²,ℤ/2]≅ℤ/2 = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = H¹[RP²,ℤ/2]→ℤ/2
  Iso.inv is = ℤ/2→H¹[RP²,ℤ/2]
  Iso.rightInv is = ℤ/2→H¹[RP²,ℤ/2]→ℤ/2
  Iso.leftInv is = H¹[RP²,ℤ/2]→ℤ/2→H¹[RP²,ℤ/2]
snd H¹[RP²,ℤ/2]≅ℤ/2 =
  isGroupHomInv ((invEquiv (fst H¹[RP²,ℤ/2]≅ℤ/2))
    , makeIsGroupHom λ x y → cong ∣_∣₂
      (funExt (elimSetRP² (λ _ → hLevelEM _ 1 _ _)
                refl
                (flipSquare
                  (emloop-comp _ x y
                  ∙ sym (cong₂+₁ (emloop x) (emloop y)))))))

----- H²(RP²,ℤ/2) ------

H²[RP²,ℤ/2]→ℤ/2 : coHom 2 ℤ/2 RP² → fst ℤ/2
H²[RP²,ℤ/2]→ℤ/2 =
  ST.rec isSetFin
    λ f → ΩEM+1→EM-gen 0 _
      (cong (ΩEM+1→EM-gen 1 _)
      ((cong (cong f) square ∙ symConst-ℤ/2 2 _ (sym (cong f line)))))

ℤ/2→H²[RP²,ℤ/2] : fst ℤ/2 → coHom 2 ℤ/2 RP²
ℤ/2→H²[RP²,ℤ/2] x = ∣ RP²Fun (0ₖ 2) refl (Iso.inv Iso-Ω²K₂-ℤ/2 x) ∣₂

H²[RP²,ℤ/2]→ℤ/2-Id : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2)))
                  → H²[RP²,ℤ/2]→ℤ/2 ∣ RP²Fun (0ₖ 2) refl p ∣₂
                  ≡ Iso.fun Iso-Ω²K₂-ℤ/2 p
H²[RP²,ℤ/2]→ℤ/2-Id q = cong (Iso.fun Iso-Ω²K₂-ℤ/2) lem
  where
  lem : q ∙ symConst-ℤ/2 2 _ refl ≡ q
  lem = (λ i → q ∙ transportRefl refl i)
       ∙ sym (rUnit q)

ℤ/2→H²[RP²,ℤ/2]→ℤ/2 : (x : fst ℤ/2)
  → H²[RP²,ℤ/2]→ℤ/2 (ℤ/2→H²[RP²,ℤ/2] x) ≡ x
ℤ/2→H²[RP²,ℤ/2]→ℤ/2 x =
    H²[RP²,ℤ/2]→ℤ/2-Id (Iso.inv Iso-Ω²K₂-ℤ/2 x)
  ∙ Iso.rightInv Iso-Ω²K₂-ℤ/2 x

H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2] : (x : coHom 2 ℤ/2 RP²)
  → ℤ/2→H²[RP²,ℤ/2] (H²[RP²,ℤ/2]→ℤ/2 x) ≡ x
H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2] =
  ST.elim (λ _ → isSetPathImplicit)
    (RP²Conn.elim₂
      (isConnectedEM 2)
      (λ _ → squash₂ _ _)
      (0ₖ 2)
      λ sq → cong (ℤ/2→H²[RP²,ℤ/2])
               (H²[RP²,ℤ/2]→ℤ/2-Id sq)
            ∙ cong ∣_∣₂ (cong (RP²Fun (snd (EM∙ ℤ/2 2)) refl)
               (Iso.leftInv Iso-Ω²K₂-ℤ/2 sq)))

H²[RP²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 2 ℤ/2 RP²) ℤ/2
fst H²[RP²,ℤ/2]≅ℤ/2 = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = H²[RP²,ℤ/2]→ℤ/2
  Iso.inv is = ℤ/2→H²[RP²,ℤ/2]
  Iso.rightInv is = ℤ/2→H²[RP²,ℤ/2]→ℤ/2
  Iso.leftInv is = H²[RP²,ℤ/2]→ℤ/2→H²[RP²,ℤ/2]
snd H²[RP²,ℤ/2]≅ℤ/2 =
  Isoℤ/2-morph (fst H²[RP²,ℤ/2]≅ℤ/2)
    _ (sym (H²[RP²,ℤ/2]→ℤ/2-Id refl)
     ∙ cong (H²[RP²,ℤ/2]→ℤ/2 ∘ ∣_∣₂)
            (characRP²Fun (λ _ → 0ₖ 2)))
       _ _ (funExt (ST.elim (λ _ → isSetPathImplicit)
             λ f → cong ∣_∣₂ (funExt
               λ x → sym (-ₖConst-ℤ/2 1 (f x))))) _


----- Hⁿ(RP²,G), n ≥ 3 -----
H³⁺ⁿ[RP²,G]≅G : (n : ℕ) (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr (3 +ℕ n) G RP²) (trivialAbGroup {ℓ})
fst (H³⁺ⁿ[RP²,G]≅G n G) =
  isoToEquiv (isContr→Iso
    (∣ RP²Fun (0ₖ (3 +ℕ n)) refl refl ∣₂
    , (ST.elim (λ _ → isSetPathImplicit)
       (RP²Conn.elim₃
         (isConnectedSubtr 4 n
           (subst (λ x → isConnected x (EM G (3 +ℕ n)))
             (+-comm 4 n)
             (isConnectedEM (3 +ℕ n))))
         (λ _ → squash₂ _ _)
         (0ₖ (3 +ℕ n))
         (cong ∣_∣₂ (characRP²Fun (λ _ → 0ₖ (3 +ℕ n)))))))
    isContrUnit*)
snd (H³⁺ⁿ[RP²,G]≅G n G) = makeIsGroupHom λ _ _ → refl
