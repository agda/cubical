{-# OPTIONS --lossy-unification #-}
{-
This file contains definition of homotopy groups in terms of joins:
π*ₙₘ(A) := ∥ Sⁿ * Sᵐ →∙ A ∥₀
and the fact that it agrees with the usual definition of homotopy groups.
-}
module Cubical.Homotopy.Group.Join where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1
open import Cubical.HITs.Join
open import Cubical.HITs.Sn.Multiplication

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath

open Iso
open GroupStr

-- Standard loop in Ω (join A B)
ℓ* : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
  → fst A → fst B → Ω (join∙ A B) .fst
ℓ* A B a b = push (pt A) (pt B)
           ∙ (push a (pt B) ⁻¹ ∙∙ push a b ∙∙ (push (pt A) b ⁻¹))

ℓS : {n m : ℕ} → S₊ n → S₊ m → Ω (join∙ (S₊∙ n) (S₊∙ m)) .fst
ℓS {n = n} {m} = ℓ* (S₊∙ n) (S₊∙ m)

-- Addition of functions join A B → C
_+*_ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  (f g : join∙ A B →∙ C) → join∙ A B →∙ C
fst (_+*_ {C = C} f g) (inl x) = pt C
fst (_+*_ {C = C} f g) (inr x) = pt C
fst (_+*_ {A = A} {B = B} f g) (push a b i) =
  (Ω→ f .fst (ℓ* A B a b) ∙ Ω→ g .fst (ℓ* A B a b)) i
snd (f +* g) = refl

-- Inversion
-* : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
      (f : join∙ A B →∙ C) → join∙ A B →∙ C
fst (-* {C = C} f) (inl x) = pt C
fst (-* {C = C} f) (inr x) = pt C
fst (-* {A = A} {B} f) (push a b i) = Ω→ f .fst (ℓ* A B a b) (~ i)
snd (-* f) = refl

-- -Π is the same as -*
-Π≡-* : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
    (f : S₊∙ (suc (n + m)) →∙ A)
  → (-Π f) ∘∙ join→Sphere∙ n m
   ≡ -* (f ∘∙ join→Sphere∙ n m)
fst (-Π≡-* f i) (inl x) = snd (-Π f) i
fst (-Π≡-* f i) (inr x) = snd (-Π f) i
fst (-Π≡-* {A = A} {n = n} {m = m} f i) (push a b j) = main i j
  where
  lem : (n : ℕ) (f : S₊∙ (suc n) →∙ A) (a : S₊ n)
    → Square (cong (fst (-Π f)) (σS a))
              (sym (snd f) ∙∙ cong (fst f) (sym (σS a)) ∙∙ snd f)
              (snd (-Π f)) (snd (-Π f))
  lem zero f false =
    doubleCompPath-filler (sym (snd f)) (cong (fst f) (sym loop)) (snd f)
  lem zero f true = doubleCompPath-filler (sym (snd f)) refl (snd f)
  lem (suc n) f a =
    (cong-∙ (fst (-Π f)) (merid a) (sym (merid (ptSn (suc n))))
      ∙ cong₂ _∙_ refl (cong (cong (fst f)) (rCancel _))
      ∙ sym (rUnit _))
    ◁ doubleCompPath-filler
      (sym (snd f)) (cong (fst f) (sym (σS a))) (snd f)

  main : Square (cong (fst (-Π f)) (σS (a ⌣S b)))
                (sym (Ω→ (f ∘∙ join→Sphere∙ n m) .fst (ℓS a b)))
                (snd (-Π f)) (snd (-Π f))
  main = lem _ f (a ⌣S b)
    ▷ sym ((λ j → (sym (lUnit (snd f) (~ j))
             ∙∙ sym (cong (fst f) (cong-∙ (join→Sphere n m)
                       (push (ptSn n) (ptSn m))
                       ((push a (ptSn m) ⁻¹)
                     ∙∙ push a b
                     ∙∙ (push (ptSn n) b ⁻¹)) j))
             ∙∙ lUnit (snd f) (~ j)))
      ∙ cong (sym (snd f) ∙∙_∙∙ snd f)
             (cong (cong (fst f))
                (congS sym
                  ((cong₂ _∙_
                    (cong σS (IdL⌣S _) ∙ σS∙)
                    (cong-∙∙ (join→Sphere n m)
                      (push a (ptSn m) ⁻¹) (push a b) (push (ptSn n) b ⁻¹)
                  ∙ (cong₂ (λ p q → p ⁻¹ ∙∙ σS (a ⌣S b) ∙∙ q ⁻¹)
                          (cong σS (IdL⌣S _) ∙ σS∙)
                          (cong σS (IdR⌣S _) ∙ σS∙))
                  ∙ sym (rUnit (σS (a ⌣S b)))))
                ∙ sym (lUnit _)))))
snd (-Π≡-* f i) j = lem i j
  where
  lem : Square (refl ∙ snd (-Π f)) refl (snd (-Π f)) refl
  lem = sym (lUnit (snd (-Π f))) ◁ λ i j → (snd (-Π f)) (i ∨ j)

-- ·Π is the same as +*
·Π≡+* : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
    (f g : S₊∙ (suc (n + m)) →∙ A)
  → (∙Π f g ∘∙ join→Sphere∙ n m)
   ≡ ((f ∘∙ join→Sphere∙ n m)
   +* (g ∘∙ join→Sphere∙ n m))
fst (·Π≡+* {A = A} f g i) (inl x) = snd (∙Π f g) i
fst (·Π≡+* {A = A} f g i) (inr x) = snd (∙Π f g) i
fst (·Π≡+* {A = A} {n = n} {m} f g i) (push a b j) = main i j
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
snd (·Π≡+* {A = A} f g i) j = lem i j
  where
  lem : Square (refl ∙ snd (∙Π f g)) refl (snd (∙Π f g)) refl
  lem = sym (lUnit (snd (∙Π f g))) ◁ λ i j → (snd (∙Π f g)) (i ∨ j)

-- Homotopy groups in terms of joins
π* : ∀ {ℓ} (n m : ℕ) (A : Pointed ℓ) → Type ℓ
π* n m A = ∥ join∙ (S₊∙ n) (S₊∙ m) →∙ A ∥₂

-- multiplication
·π* : ∀ {ℓ} {n m : ℕ} {A : Pointed ℓ} (f g : π* n m A) → π* n m A
·π* = ST.rec2 squash₂ λ f g → ∣ f +* g ∣₂

-π* : ∀ {ℓ} {n m : ℕ} {A : Pointed ℓ} (f : π* n m A) → π* n m A
-π* = ST.map -*

1π* : ∀ {ℓ} {n m : ℕ} {A : Pointed ℓ} → π* n m A
1π* = ∣ const∙ _ _ ∣₂

Iso-JoinMap-SphereMap : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
  → Iso (join∙ (S₊∙ n) (S₊∙ m) →∙ A)
         (S₊∙ (suc (n + m)) →∙ A)
Iso-JoinMap-SphereMap n m = post∘∙equiv (joinSphereEquiv∙ n m)

Iso-π*-π' : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
  → Iso ∥ (join∙ (S₊∙ n) (S₊∙ m) →∙ A) ∥₂
         ∥ (S₊∙ (suc (n + m)) →∙ A) ∥₂
Iso-π*-π' n m = setTruncIso (Iso-JoinMap-SphereMap n m)

private
  J≃∙map : ∀ {ℓ ℓ' ℓ''} {A1 A2 : Pointed ℓ} {A : Pointed ℓ'}
         → (e : A1 ≃∙ A2) {P : A1 →∙ A → Type ℓ''}
       → ((f : A2 →∙ A) → P (f ∘∙ ≃∙map e))
       → (f : _) → P f
  J≃∙map  {ℓ'' = ℓ''} {A2 = A2} {A = A} =
    Equiv∙J (λ A1 e → {P : A1 →∙ A → Type ℓ''}
         → ((f : A2 →∙ A) → P (f ∘∙ ≃∙map e))
          → (f : _) → P f)
      λ {P} ind f
      → subst P (ΣPathP (refl , sym (lUnit (snd f)))) (ind f)

π*≡π' : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
  (f g : π* n m A)
  → Iso.fun (Iso-π*-π' n m) (·π* f g)
  ≡ ·π' _ (Iso.fun (Iso-π*-π' n m) f) (Iso.fun (Iso-π*-π' n m) g)
π*≡π' {A = A} {n} {m} = ST.elim2 (λ _ _ → isSetPathImplicit)
  (J≃∙map (joinSphereEquiv∙ n m)
    λ f → J≃∙map (joinSphereEquiv∙ n m)
      λ g → cong ∣_∣₂
        (cong (fun (Iso-JoinMap-SphereMap n m)) (sym (·Π≡+* f g))
        ∙ ∘∙-assoc _ _ _
        ∙ cong (∙Π f g ∘∙_) ret
        ∙ ∘∙-idˡ (∙Π f g)
        ∙ cong₂ ∙Π
              ((sym (∘∙-idˡ f) ∙ cong (f ∘∙_) (sym ret)) ∙ sym (∘∙-assoc _ _ _))
              (sym (∘∙-idˡ g) ∙ cong (g ∘∙_) (sym ret) ∙ sym (∘∙-assoc _ _ _))))
  where
  ret = ≃∙→ret/sec∙ {B = _ , ptSn (suc (n + m))}
          (joinSphereEquiv∙ n m) .snd

-π*≡-π' : ∀ {ℓ} {A : Pointed ℓ} {n m : ℕ}
  (f : π* n m A)
  → Iso.fun (Iso-π*-π' n m) (-π* f)
  ≡ -π' _ (Iso.fun (Iso-π*-π' n m) f)
-π*≡-π' {n = n} {m} =
  ST.elim (λ _ → isSetPathImplicit)
   (J≃∙map (joinSphereEquiv∙ n m)
    λ f → cong ∣_∣₂
      (cong (_∘∙ (≃∙map (invEquiv∙ (joinSphereEquiv∙ n m))))
            (sym (-Π≡-* f))
    ∙ ∘∙-assoc _ _ _
    ∙ cong (-Π f ∘∙_) ret
    ∙ ∘∙-idˡ (-Π f)
    ∙ cong -Π (sym (∘∙-assoc _ _ _ ∙ cong (f ∘∙_) ret ∙ ∘∙-idˡ f))))
  where
  ret = ≃∙→ret/sec∙ {B = _ , ptSn (suc (n + m))}
          (joinSphereEquiv∙ n m) .snd

-- Homotopy groups in terms of joins
π*Gr : ∀ {ℓ} (n m : ℕ) (A : Pointed ℓ) → Group ℓ
fst (π*Gr n m A) = π* n m A
1g (snd (π*Gr n m A)) = 1π*
GroupStr._·_ (snd (π*Gr n m A)) = ·π*
inv (snd (π*Gr n m A)) = -π*
isGroup (snd (π*Gr n m A)) =
  transport (λ i → IsGroup (p1 (~ i)) (p2 (~ i)) (p3 (~ i)))
            (isGroup (π'Gr (n + m) A .snd))
  where
  p1 : PathP (λ i → isoToPath (Iso-π*-π' {A = A} n m) i)
             1π* (1π' (suc (n + m)))
  p1 = toPathP (cong ∣_∣₂ (transportRefl _ ∙ ΣPathP (refl , sym (rUnit refl))))

  p2 : PathP (λ i → (f g : isoToPath (Iso-π*-π' {A = A} n m) i)
                  → isoToPath (Iso-π*-π' {A = A} n m) i)
              ·π* (·π' _)
  p2 = toPathP (funExt λ f
    → funExt λ g → transportRefl _
    ∙ π*≡π' _ _
    ∙ cong₂ (·π' (n + m))
            (Iso.rightInv (Iso-π*-π' n m) _ ∙ transportRefl f)
            (Iso.rightInv (Iso-π*-π' n m) _ ∙ transportRefl g))

  p3 : PathP (λ i → isoToPath (Iso-π*-π' {A = A} n m) i
                   → isoToPath (Iso-π*-π' {A = A} n m) i)
             -π* (-π' _)
  p3 = toPathP (funExt λ f → transportRefl _
    ∙ -π*≡-π' _
    ∙ cong (-π' (n + m))
           (Iso.rightInv (Iso-π*-π' n m) _ ∙ transportRefl f))

-- Homotopy groups in terms of joins agrees with usual definition
π*Gr≅π'Gr : ∀ {ℓ} (n m : ℕ) (A : Pointed ℓ)
  → GroupIso (π*Gr n m A) (π'Gr (n + m) A)
fst (π*Gr≅π'Gr n m A) = Iso-π*-π' {A = A} n m
snd (π*Gr≅π'Gr n m A) = makeIsGroupHom π*≡π'

-- Functoriality
π*∘∙fun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n m : ℕ) (f : A →∙ B)
   → π* n m A → π* n m B
π*∘∙fun n m f  = ST.map (f ∘∙_)

π*∘∙Hom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n m : ℕ) (f : A →∙ B)
  → GroupHom (π*Gr n m A) (π*Gr n m B)
fst (π*∘∙Hom {A = A} {B = B} n m f) = π*∘∙fun n m f
snd (π*∘∙Hom {A = A} {B = B} n m f) =
  subst (λ ϕ → IsGroupHom (π*Gr n m A .snd) ϕ (π*Gr n m B .snd))
        π*∘∙Hom'≡
        (snd π*∘∙Hom')
  where
  GroupHomπ≅π*PathP : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
    → GroupHom (π'Gr (n + m) A) (π'Gr (n + m) B)
     ≡ GroupHom (π*Gr n m A) (π*Gr n m B)
  GroupHomπ≅π*PathP A B n m i =
    GroupHom (fst (GroupPath _ _) (GroupIso→GroupEquiv (π*Gr≅π'Gr n m A)) (~ i))
             (fst (GroupPath _ _) (GroupIso→GroupEquiv (π*Gr≅π'Gr n m B)) (~ i))

  π*∘∙Hom' : _
  π*∘∙Hom' = transport (λ i → GroupHomπ≅π*PathP A B n m i)
                       (π'∘∙Hom (n + m) f)

  π*∘∙Hom'≡ : π*∘∙Hom' .fst ≡ π*∘∙fun n m f
  π*∘∙Hom'≡ =
    funExt (ST.elim (λ _ → isSetPathImplicit)
           λ g → cong ∣_∣₂ (cong (inv (Iso-JoinMap-SphereMap n m))
                   (transportRefl _
                   ∙ cong (f ∘∙_) (transportRefl _))
                 ∙ ∘∙-assoc _ _ _
                 ∙ cong (f ∘∙_ )
                        (∘∙-assoc _ _ _ ∙ cong (g ∘∙_)
                         (≃∙→ret/sec∙ {B = _ , ptSn (suc (n + m))}
                          (joinSphereEquiv∙ n m) .fst)
                       ∙ ∘∙-idˡ g)))

π*∘∙Equiv : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n m : ℕ) (f : A ≃∙ B)
  → GroupEquiv (π*Gr n m A) (π*Gr n m B)
fst (π*∘∙Equiv n m f) = isoToEquiv (setTruncIso (pre∘∙equiv f))
snd (π*∘∙Equiv n m f) = π*∘∙Hom n m (≃∙map f) .snd
