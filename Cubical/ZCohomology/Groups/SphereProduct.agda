{-
This file shows Hⁿ⁺ᵐ(Sⁿ×Sᵐ)≅ℤ for n, m ≥ 1. This can be done in several
ways (e.g. Mayer-Vietoris). We give the iso as explicitly
as possible. The idea:
Step 1: Hⁿ⁺ᵐ(Sⁿ×Sᵐ)≅H¹⁺ⁿ⁺ᵐ(S¹⁺ⁿ×Sᵐ) (i.e. some form of suspension
axiom).
Step 2: H¹⁺ᵐ(S¹×Sᵐ)≅ℤ
Step 3: Conclude Hⁿ⁺ᵐ(Sⁿ×Sᵐ)≅ℤ by induction on n.

The iso as defined here has the advantage that it looks a lot like
the cup product, making it trivial to show that e.g. gₗ ⌣ gᵣ ≡ e, where
gₗ, gᵣ are the two generators of H²(S²×S²) and e is the generator of
H⁴(S²×S²) -- this of interest since it is used in π₄S³≅ℤ/2.
-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.SphereProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.HITs.Truncation as T
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct

open Iso
open PlusBis

private
  ¬lem : (n m : ℕ) → ¬ suc (n + m) ≡ m
  ¬lem n zero = snotz
  ¬lem n (suc m) p =
    ¬lem n m (sym (+-suc n m) ∙ cong predℕ p)



{- Step 1: Hⁿ⁺ᵐ(Sⁿ×Sᵐ)≅H¹⁺ⁿ⁺ᵐ(S¹⁺ⁿ×Sᵐ) -}
-- The functions back and forth (suspension on the left component)
↓Sⁿ×Sᵐ→Kₙ₊ₘ : (n m : ℕ)
  → (S₊ (suc (suc n)) → S₊ (suc m) → coHomK (suc (suc ((suc n) + m))))
  → S₊ (suc n) → S₊ (suc m) → coHomK (suc (suc (n + m)))
↓Sⁿ×Sᵐ→Kₙ₊ₘ n m f x y =
  ΩKn+1→Kn ((suc ((suc n) + m)))
    (sym (rCancelₖ _ (f north y))
    ∙∙ cong (λ x → f x y -ₖ f north y) (merid x ∙ sym (merid (ptSn (suc n))))
    ∙∙ rCancelₖ _ (f north y))

↑Sⁿ×Sᵐ→Kₙ₊ₘ : (n m : ℕ)
  → (S₊ (suc n) → S₊ (suc m) → coHomK (suc (suc (n + m))))
  → (S₊ (suc (suc n)) → S₊ (suc m) → coHomK (suc (suc ((suc n) + m))))
↑Sⁿ×Sᵐ→Kₙ₊ₘ n m f north y = 0ₖ _
↑Sⁿ×Sᵐ→Kₙ₊ₘ n m f south y = 0ₖ _
↑Sⁿ×Sᵐ→Kₙ₊ₘ n m f (merid a i) y =
  Kn→ΩKn+1 _ (f a y) i

∥HⁿSᵐPath∥ : (n m : ℕ) → (f : S₊ (suc m) → coHomK (suc n))
       → ¬ (n ≡ m)
       → ∥ f ≡ (λ _ → 0ₖ (suc n)) ∥₁
∥HⁿSᵐPath∥ n m f p =
  fun PathIdTrunc₀Iso
    (isContr→isProp
      (isOfHLevelRetractFromIso 0 (fst (Hⁿ-Sᵐ≅0 n m p)) isContrUnit)
        ∣ f ∣₂ (0ₕ _))

-- The iso
×leftSuspensionIso : (n m : ℕ)
  → GroupIso (coHomGr (suc (((suc n) + m)))
                  (S₊ (suc n) × S₊ (suc m)))
              (coHomGr (suc (suc ((suc n) + m)))
                  (S₊ (suc (suc n)) × S₊ (suc m)))
fun (fst (×leftSuspensionIso n m)) =
  ST.map (uncurry ∘ ↑Sⁿ×Sᵐ→Kₙ₊ₘ n m ∘ curry)
inv (fst (×leftSuspensionIso n m)) =
  ST.map ((uncurry ∘ ↓Sⁿ×Sᵐ→Kₙ₊ₘ n m ∘ curry))
rightInv (fst (×leftSuspensionIso n m)) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → inv PathIdTrunc₀Iso
      (PT.rec squash₁
        (uncurry (λ g p
          → PT.map (λ gid → funExt λ {(x , y)
         → (λ i → uncurry (↑Sⁿ×Sᵐ→Kₙ₊ₘ n m
                    (↓Sⁿ×Sᵐ→Kₙ₊ₘ n m (curry (p (~ i))))) (x , y))
                ∙∙ main g gid x y
                ∙∙ funExt⁻ p (x , y)})
                   (∥Path∥ g)))
        (rewrte f))
  where
  lem : (n m : ℕ) → ¬ suc (suc (n + m)) ≡ m
  lem n zero = snotz
  lem n (suc m) p = lem n m (cong suc (sym (+-suc n m)) ∙ cong predℕ p)

  charac-fun :
      (S₊ (suc n) → S₊ (suc m)
              → typ (Ω (coHomK-ptd (suc (suc (suc n + m))))))
    → S₊ (suc (suc n)) × S₊ (suc m) → coHomK (suc (suc (suc n + m)))
  charac-fun g (north , y) = 0ₖ _
  charac-fun g (south , y) = 0ₖ _
  charac-fun g (merid c i , y) = g c y i

  rewrte : (f : S₊ (suc (suc n)) × S₊ (suc m)
           → coHomK (suc (suc (suc n + m))))
       → ∃[ g ∈ (S₊ (suc n) → S₊ (suc m)
              → typ (Ω (coHomK-ptd (suc (suc (suc n + m)))))) ]
            charac-fun g ≡ f
  rewrte f =
    PT.map (λ p
      → (λ x y → sym (funExt⁻ p y)
                ∙∙ (λ i → f ((merid x ∙ sym (merid (ptSn (suc n)))) i , y))
                ∙∙ funExt⁻ p y)
       , funExt λ { (north , y) → sym (funExt⁻ p y)
                  ; (south , y) → sym (funExt⁻ p y)
                                ∙ λ i → f (merid (ptSn (suc n)) i , y)
                  ; (merid a i , y) j
              → hcomp (λ k → λ { (i = i0) → p (~ j ∧ k) y
                                 ; (i = i1)
                                  → compPath-filler'
                                      (sym (funExt⁻ p y))
                                      (λ i → f (merid (ptSn (suc n)) i , y)) k j
                                 ; (j = i1) → f (merid a i , y) })
                       (f (compPath-filler (merid a)
                          (sym (merid (ptSn (suc n)))) (~ j) i
                         , y))})
      (∥HⁿSᵐPath∥ _ _ (λ x → f (north , x))
        (lem n m))

  ∥Path∥ :
    (g : S₊ (suc n) → S₊ (suc m)
         → typ (Ω (coHomK-ptd (suc (suc (suc n + m))))))
       → ∥ (g (ptSn _)) ≡ (λ _ → refl) ∥₁
  ∥Path∥ g =
      fun PathIdTrunc₀Iso
        (isContr→isProp
          (isOfHLevelRetractFromIso 0
            ((invIso (fst (coHom≅coHomΩ _ (S₊ (suc m))))))
             (0ₕ _ , ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                 λ f → PT.rec (squash₂ _ _) (sym ∘ cong ∣_∣₂)
                   (∥HⁿSᵐPath∥ _ _ f (¬lem n m))))
          ∣ g (ptSn (suc n)) ∣₂ ∣ (λ _ → refl) ∣₂)

  main : (g : _) → (g (ptSn _)) ≡ (λ _ → refl)
     → (x : S₊ (suc (suc n))) (y : S₊ (suc m))
    → uncurry (↑Sⁿ×Sᵐ→Kₙ₊ₘ n m
         (↓Sⁿ×Sᵐ→Kₙ₊ₘ n m (curry (charac-fun g)))) (x , y)
      ≡ charac-fun g (x , y)
  main g gid north y = refl
  main g gid south y = refl
  main g gid (merid a i) y j = helper j i
    where
    helper : (λ i → uncurry (↑Sⁿ×Sᵐ→Kₙ₊ₘ n m
                    (↓Sⁿ×Sᵐ→Kₙ₊ₘ n m (curry (charac-fun g))))
                     (merid a i , y))
      ≡ g a y
    helper = (λ i → rightInv (Iso-Kn-ΩKn+1 _)
                  ((sym (rCancel≡refl _ i)
           ∙∙ cong-∙ (λ x → rUnitₖ _ (charac-fun g (x , y)) i)
                (merid a) (sym (merid (ptSn (suc n)))) i
           ∙∙ rCancel≡refl _ i)) i)
        ∙∙ sym (rUnit _)
        ∙∙ (cong (g a y ∙_) (cong sym (funExt⁻ gid y))
          ∙ sym (rUnit (g a y)))
leftInv (fst (×leftSuspensionIso n m)) =
  ST.elim (λ _ → isSetPathImplicit)
        λ f → PT.rec (squash₂ _ _)
          (λ id
            → cong ∣_∣₂
              (funExt (λ {(x , y) → (λ i → ΩKn+1→Kn _ (sym (rCancel≡refl _ i)
                       ∙∙ ((λ j → rUnitₖ _
                             (↑Sⁿ×Sᵐ→Kₙ₊ₘ n m (curry f)
                               ((merid x ∙ sym (merid (ptSn (suc n)))) j) y) i))
                       ∙∙ rCancel≡refl _ i))
                ∙ (λ i → ΩKn+1→Kn _  (rUnit
                           (cong-∙ (λ r → ↑Sⁿ×Sᵐ→Kₙ₊ₘ n m (curry f) r y)
                              (merid x) (sym (merid (ptSn (suc n)))) i) (~ i)))
                ∙ cong (ΩKn+1→Kn _) (cong (Kn→ΩKn+1 _ (f (x , y)) ∙_)
                       (cong sym (cong (Kn→ΩKn+1 _)
                                  (funExt⁻ id y) ∙ (Kn→ΩKn+10ₖ _)))
                         ∙ sym (rUnit _))
                ∙ leftInv (Iso-Kn-ΩKn+1 _) (f (x , y))})))
          (∥HⁿSᵐPath∥ (suc n + m) m (λ x → f (ptSn _ , x))
            (¬lem n m))
snd (×leftSuspensionIso n m) =
  makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂
      (funExt λ { (north , y) → refl
                ; (south , y) → refl
                ; (merid a i , y) j
                 → (sym (∙≡+₂ _ (Kn→ΩKn+1 _ (f (a , y)))
                         (Kn→ΩKn+1 _ (g (a , y))))
                   ∙ sym (Kn→ΩKn+1-hom _
                          (f (a , y)) (g (a , y)))) (~ j) i}))

{- Step 2: H¹⁺ᵐ(S¹×Sᵐ)≅ℤ -}

-- The functions back and forth
Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ : (m : ℕ)
  → (S₊ (suc m) → coHomK (suc m))
  → S₊ (suc zero) → S₊ (suc m) → coHomK (suc (suc m))
Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m f base y = 0ₖ _
Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m f (loop i) y = Kn→ΩKn+1 (suc m) (f y) i

Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ : (m : ℕ)
  → (S₊ (suc zero) → S₊ (suc m) → coHomK (suc (suc m)))
  → (S₊ (suc m) → coHomK (suc m))
Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ m f x =
  ΩKn+1→Kn (suc m)
       (sym (rCancelₖ _ (f base x))
    ∙∙ ((λ i → f (loop i) x -ₖ f base x))
    ∙∙ rCancelₖ _ (f base x))

Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ : (m : ℕ)
  → GroupIso (coHomGr (suc m) (S₊ (suc m)))
              (coHomGr (suc (suc m)) (S₊ (suc zero) × S₊ (suc m)))
fun (fst (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m)) = ST.map (uncurry ∘ Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m)
inv (fst (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m)) = ST.map (Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ m ∘ curry)
rightInv (fst (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m)) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → inv PathIdTrunc₀Iso
      (PT.map (uncurry (λ g p
        → funExt λ {(x , y)
          → (λ i → uncurry
                      (Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m
                        (Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ m (curry (p i)))) (x , y))
          ∙∙ main g x y
          ∙∙ sym (funExt⁻ p (x , y))}))
        (rewrte f))
  where
  characFun : (x : S₊ (suc m) → coHomK (suc m))
           → S₊ 1 × S₊ (suc m) → coHomK (suc (suc m))
  characFun f (base , y) = 0ₖ _
  characFun f (loop i , y) = Kn→ΩKn+1 _ (f y) i

  main : (g : _) (x : S¹) (y : S₊ (suc m))
    → uncurry (Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m (Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ m (curry (characFun g))))
         (x , y)
      ≡ characFun g (x , y)
  main g base y = refl
  main g (loop i) y j = help j i
    where
    help : cong (λ x → Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m
                         (Hⁿ-Sⁿ→Hⁿ-S¹×Sⁿ m (curry (characFun g))) x y) loop
         ≡ Kn→ΩKn+1 _ (g y)
    help = rightInv (Iso-Kn-ΩKn+1 (suc m))
                 (sym (rCancelₖ _ (0ₖ _))
              ∙∙ ((λ i → Kn→ΩKn+1 _ (g y) i -ₖ 0ₖ _))
              ∙∙ rCancelₖ _ (0ₖ _))
        ∙∙ (λ i → sym (rCancel≡refl _ i)
                ∙∙ (λ j → rUnitₖ _ (Kn→ΩKn+1 _ (g y) j) i)
                ∙∙ rCancel≡refl _ i)
        ∙∙ sym (rUnit _)

  lem : (m : ℕ) → ¬ suc m ≡ m
  lem zero = snotz
  lem (suc m) p = lem m (cong predℕ p)

  rewrte : (f : S₊ 1 × S₊ (suc m) → coHomK (suc (suc m)))
     → ∃[ g ∈ (S₊ (suc m) → coHomK (suc m)) ] f ≡ characFun g
  rewrte f =
    PT.map (λ p →
       (λ x → ΩKn+1→Kn _
                (sym (funExt⁻ p x) ∙∙ (λ i → f (loop i , x)) ∙∙ funExt⁻ p x))
      , funExt λ { (base , y) → funExt⁻ p y
                 ; (loop i , x) j →
                   hcomp (λ k → λ {(i = i0) → funExt⁻ p x j
                                  ; (i = i1) → funExt⁻ p x j
                                  ; (j = i0) → f (loop i , x)
                                  ; (j = i1) →
                                      rightInv (Iso-Kn-ΩKn+1 (suc m))
                                        (sym (funExt⁻ p x)
                                        ∙∙ (λ i → f (loop i , x))
                                        ∙∙ funExt⁻ p x) (~ k) i})
                          (doubleCompPath-filler
                            (sym (funExt⁻ p x))
                            (λ i → f (loop i , x))
                            (funExt⁻ p x) j i)})
     (∥HⁿSᵐPath∥ (suc m) m (λ x → f (base , x)) (lem m))
leftInv (fst (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m)) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f
      → cong ∣_∣₂ (funExt λ x
        → cong (ΩKn+1→Kn (suc m))
               ((λ i → sym (rCancel≡refl _ i)
                 ∙∙ cong (λ z → rUnitₖ _ (Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ m f z x) i) loop
                 ∙∙ rCancel≡refl _ i) ∙ sym (rUnit (Kn→ΩKn+1 (suc m) (f x))))
        ∙ leftInv (Iso-Kn-ΩKn+1 _) (f x))
snd (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m) =
  makeIsGroupHom
    (ST.elim2
      (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂
        (funExt λ { (base , y) → refl
                  ; (loop i , y) j →
                          (sym (∙≡+₂ _ (Kn→ΩKn+1 _ (f y)) (Kn→ΩKn+1 _ (g y)))
                         ∙ sym (Kn→ΩKn+1-hom _ (f y) (g y))) (~ j) i}))

Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ : (n m : ℕ)
  → GroupIso (coHomGr ((suc n) +' (suc m))
                  (S₊ (suc n) × S₊ (suc m)))
              ℤGroup
Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ zero m =
  compGroupIso (invGroupIso (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ m)) (Hⁿ-Sⁿ≅ℤ m)
Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ (suc n) m =
  compGroupIso
          (invGroupIso (×leftSuspensionIso n m))
            (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ n m)

-- Proof that ⌣ respects generators for H²×H²→H⁴
-- Todo: generalise

H²-S²×S²-genₗ : coHom 2 (S₊ 2 × S₊ 2)
H²-S²×S²-genₗ = ∣ (λ x → ∣ fst x ∣) ∣₂

H²-S²×S²-genᵣ : coHom 2 (S₊ 2 × S₊ 2)
H²-S²×S²-genᵣ = ∣ (λ x → ∣ snd x ∣) ∣₂

H²-S²≅H⁴-S²×S² : GroupIso (coHomGr 2 (S₊ 2)) (coHomGr 4 (S₊ 2 × S₊ 2))
H²-S²≅H⁴-S²×S² = (compGroupIso (Hⁿ-Sⁿ≅Hⁿ-S¹×Sⁿ 1) (×leftSuspensionIso 0 1))

H²-S²≅H⁴-S²×S²⌣ :
  fun (fst (H²-S²≅H⁴-S²×S²)) ∣ ∣_∣ₕ ∣₂ ≡ H²-S²×S²-genₗ ⌣ H²-S²×S²-genᵣ
H²-S²≅H⁴-S²×S²⌣ =
  cong ∣_∣₂ (funExt (uncurry
    (λ { north y → refl
       ; south y → refl
       ; (merid a i) y j → Kn→ΩKn+1 3 (lem a y j) i})))
  where
  lem : (a : S¹) (y : S₊ 2)
      → Hⁿ-S¹×Sⁿ→Hⁿ-Sⁿ 1 ∣_∣ₕ a y ≡ _⌣ₖ_ {n = 1} {m = 2} ∣ a ∣ₕ ∣ y ∣ₕ
  lem base y = refl
  lem (loop i) y = refl
