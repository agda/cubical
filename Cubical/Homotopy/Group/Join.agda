{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.Group.Join where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S3
open import Cubical.HITs.Join

open import Cubical.HITs.Sn.Multiplication



open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr

join∙ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  → Pointed _
fst (join∙ A B) = join (fst A) (fst B)
snd (join∙ A B) = inl (pt A)

ℓ* : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  → fst A → fst B → Ω (join∙ A B) .fst
ℓ* A B a b = push (pt A) (pt B)
           ∙ (push a (pt B) ⁻¹ ∙∙ push a b ∙∙ (push (pt A) b ⁻¹))

ℓS : {n m : ℕ} → S₊ n → S₊ m → Ω (join∙ (S₊∙ n) (S₊∙ m)) .fst
ℓS {n = n} {m} = ℓ* (S₊∙ n) (S₊∙ m)

_+*_ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (f g : join∙ A B →∙ C) → join∙ A B →∙ C
fst (_+*_ {C = C} f g) (inl x) = pt C
fst (_+*_ {C = C} f g) (inr x) = pt C
fst (_+*_ {A = A} {B = B} f g) (push a b i) =
  (Ω→ f .fst (ℓ* A B a b) ∙ Ω→ g .fst (ℓ* A B a b)) i
snd (f +* g) = refl

join→Sphere∙ : (n m : ℕ)
  → join∙ (S₊∙ n) (S₊∙ m) →∙ S₊∙ (suc (n + m))
fst (join→Sphere∙ n m) = join→Sphere n m
snd (join→Sphere∙ n m) = refl

·Π* : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
    (f g : S₊∙ (suc (n + m)) →∙ A)
  → (∙Π f g ∘∙ join→Sphere∙ n m)
   ≡ ((f ∘∙ join→Sphere∙ n m)
   +* (g ∘∙ join→Sphere∙ n m))
fst (·Π* {A = A} f g i) (inl x) = snd (∙Π f g) i
fst (·Π* {A = A} f g i) (inr x) = snd (∙Π f g) i
fst (·Π* {A = A} {n = n} {m} f g i) (push a b j) = main i j
  where
  help : (n : ℕ) (f g : S₊∙ (suc n) →∙ A) (a : S₊ n)
    → Square (cong (fst (∙Π f g)) (σS a))
              (Ω→ f .fst (σS a) ∙ Ω→ g .fst (σS a))
              (snd (∙Π f g)) (snd (∙Π f g))
  help zero f g false = refl
  help zero f g true =
      rUnit refl
    ∙ cong₂ _∙_ (sym (∙∙lCancel (snd f))) (sym (∙∙lCancel (snd g)))
  help (suc n) f g a =
      cong-∙ (fst (∙Π f g)) (merid a) (sym (merid (ptSn (suc n))))
    ∙ cong (cong (fst (∙Π f g)) (merid a) ∙_)
        (congS sym
          (cong₂ _∙_
            (cong (sym (snd f) ∙∙_∙∙ snd f)
              (cong (cong (fst f)) (rCancel (merid (ptSn (suc n)))))
              ∙ Ω→ f .snd)
            (cong (sym (snd g) ∙∙_∙∙ snd g)
              (cong (cong (fst g)) (rCancel (merid (ptSn (suc n)))))
              ∙ Ω→ g .snd)
           ∙ sym (rUnit refl)))
    ∙ sym (rUnit _)

  Ω→σ : ∀ {ℓ} {A : Pointed ℓ} (f : S₊∙ (suc (n + m)) →∙ A)
    → Ω→ f .fst (σS (a ⌣S b))
     ≡ Ω→ (f ∘∙ join→Sphere∙ n m) .fst (ℓS a b)
  Ω→σ f =
      cong (sym (snd f) ∙∙_∙∙ snd f)
        (cong (cong (fst f))
          (sym main))
    ∙ λ i → Ω→ (lem (~ i)) .fst (ℓS a b)
    where
    main : cong (join→Sphere n m) (ℓS a b) ≡ σS (a ⌣S b)
    main = cong-∙ (join→Sphere n m) _ _
         ∙ cong₂ _∙_
             (cong σS (IdL⌣S _) ∙ σS∙)
             (cong-∙∙ (join→Sphere n m) _ _ _
           ∙ (λ i → sym ((cong σS (IdL⌣S a) ∙ σS∙) i)
                  ∙∙ σS (a ⌣S b)
                  ∙∙ sym ((cong σS (IdR⌣S b) ∙ σS∙) i))
           ∙ sym (rUnit (σS (a ⌣S b))) )
         ∙ sym (lUnit (σS (a ⌣S b)))
    lem : f ∘∙ join→Sphere∙ n m ≡ (fst f ∘ join→Sphere n m , snd f)
    lem = ΣPathP (refl , (sym (lUnit _)))

  main : Square (cong (fst (∙Π f g)) (σS (a ⌣S b)))
                (Ω→ (f ∘∙ join→Sphere∙ n m) .fst (ℓS a b)
               ∙ Ω→ (g ∘∙ join→Sphere∙ n m) .fst (ℓS a b))
                (snd (∙Π f g)) (snd (∙Π f g))
  main = help _ f g (a ⌣S b) ▷ cong₂ _∙_ (Ω→σ f) (Ω→σ g)
snd (·Π* {A = A} f g i) j = lem i j
  where
  lem : Square (refl ∙ snd (∙Π f g)) refl (snd (∙Π f g)) refl
  lem = sym (lUnit (snd (∙Π f g))) ◁ λ i j → (snd (∙Π f g)) (i ∨ j)

-- Homotopy groups in terms of joins
π* : ∀ {ℓ} (n m : ℕ) (A : Pointed ℓ) → Type ℓ
π* n m A = ∥ join∙ (S₊∙ n) (S₊∙ m) →∙ A ∥₂

-- multiplication
·π* : ∀ {ℓ} {n m : ℕ} {A : Pointed ℓ} (f g : π* n m A) → π* n m A
·π* = ST.rec2 squash₂ λ f g → ∣ f +* g ∣₂

Iso-JoinMap-SphereMap : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
  → Iso (join∙ (S₊∙ n) (S₊∙ m) →∙ A)
         (S₊∙ (suc (n + m)) →∙ A)
Iso-JoinMap-SphereMap n m =
  post∘∙equiv (isoToEquiv (joinSphereIso n m) , refl)

Iso-π*-π' : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
  → Iso ∥ (join∙ (S₊∙ n) (S₊∙ m) →∙ A) ∥₂
         ∥ (S₊∙ (suc (n + m)) →∙ A) ∥₂
Iso-π*-π' n m = setTruncIso (Iso-JoinMap-SphereMap n m)

π*≡π' : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
  (f g : π* n m A)
  → Iso.fun (Iso-π*-π' n m) (·π* f g)
  ≡ ·π' _ (Iso.fun (Iso-π*-π' n m) f) (Iso.fun (Iso-π*-π' n m) g)
π*≡π' = ST.elim2 (λ _ _ → isSetPathImplicit)
                 λ f g → cong ∣_∣₂ {!·Π* -- f g!}
