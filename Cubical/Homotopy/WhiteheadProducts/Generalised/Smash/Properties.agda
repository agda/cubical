{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Properties

open Iso

module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
  (B : Pointed ℓ') {C : Pointed ℓ''}
  (f g : Susp∙ (Susp (typ A)) →∙ C)
  (h : Susp∙ (typ B) →∙ C) where
  -- ·whΣ version
  WhiteheadProdΣBilinₗ : ·whΣ (Susp∙ (typ A)) B (·Susp (Susp∙ (typ A)) f g) h
                      ≡ ·Susp (Susp∙ (typ A) ⋀∙ B)
                              (·whΣ (Susp∙ (typ A)) B f h)
                              (·whΣ (Susp∙ (typ A)) B g h)
  WhiteheadProdΣBilinₗ =
    transport (λ j
      → PathP-·wh-·whΣ (Susp∙ (typ A)) B
          (·Susp (Susp∙ (typ A)) f g) h (~ j)
      ≡ ·Susp-+*-PathP {A = Susp∙ (typ A)} {B} {C} (~ j)
        (PathP-·wh-·whΣ (Susp∙ (typ A)) B f h (~ j))
        (PathP-·wh-·whΣ  (Susp∙ (typ A)) B g h (~ j)))
      (WhiteheadProdBilinₗ A B {C} f g h)

module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
  (B : Pointed ℓ') {C : Pointed ℓ''}
  (f : Susp∙ (typ A) →∙ C)
  (g h : Susp∙ (Susp (typ B)) →∙ C) where
  -- ·whΣ version
  WhiteheadProdΣBilinᵣ : ·whΣ A (Susp∙ (typ B)) f (·Susp (Susp∙ (typ B)) g h)
                       ≡ ·Susp (A ⋀∙ Susp∙ (typ B))
                               (·whΣ A (Susp∙ (typ B)) f g)
                               (·whΣ A (Susp∙ (typ B)) f h)
  WhiteheadProdΣBilinᵣ =
    transport (λ j
      → PathP-·wh-·whΣ A (Susp∙ (typ B)) f
          (·Susp (Susp∙ (typ B)) g h) (~ j)
      ≡ ·Susp-+*-PathP {A = A} {Susp∙ (typ B)} {C} (~ j)
        (PathP-·wh-·whΣ  A (Susp∙ (typ B)) f g (~ j))
        (PathP-·wh-·whΣ  A (Susp∙ (typ B)) f h (~ j)))
      (WhiteheadProdBilinᵣ A B f g h)

WhiteheadProdΣIdL : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (typ B) →∙ C)
      → ·whΣ A B (const∙ _ _) f ≡ const∙ _ _
WhiteheadProdΣIdL A B {C = C} f =
  transport (λ i → PathP-·wh-·whΣ A B (const∙ _ _) f (~ i)
                 ≡ ·Susp-0*-PathP (~ i))
            (WhiteheadProdIdL A B f)

WhiteheadProdΣIdR : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (typ A) →∙ C)
      → ·whΣ A B f (const∙ _ _) ≡ const∙ _ _
WhiteheadProdΣIdR A B {C = C} f =
  transport (λ i → PathP-·wh-·whΣ A B f (const∙ _ _) (~ i)
                 ≡ ·Susp-0*-PathP (~ i))
            (WhiteheadProdIdR A B f)

module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (Susp (typ A)) →∙ C)
         (g : Susp∙ (Susp (typ B)) →∙ C)
  where
  WhiteheadProdΣComm : ·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g
                     ≡ -Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B))
                             (·whΣ (Susp∙ (typ B)) (Susp∙ (typ A)) g f
                            ∘∙ suspFun∙ ⋀comm→)
  WhiteheadProdΣComm =
      sym (·wh≡·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g)
    ∙ cong₂ _∘∙_ (WhiteheadProdComm A B f g) refl
    ∙ ∘∙-assoc _ _ _
    ∙ cong (·wh (Susp∙ (typ B)) (Susp∙ (typ A)) g f ∘∙_)
           (ΣPathP ((funExt (λ { north → push north north
                               ; south → refl
                               ; (merid a i) j
                              → ((compPath-filler' (push north north)
                                    (cong (SuspSmash→Join
                                        ∘ fst ((-Susp (Susp∙ (typ A)
                                                    ⋀∙ Susp∙ (typ B)))
                                    (suspFun∙ ⋀comm→)))
                                     (merid a)))
                                ▷ (funExt⁻ (sym F1≡F2) a)) (~ j) i}))
                  , ptLem)
          ∙ sym (-Susp-∘∙ _ _ _))
    ∙ sym (-Susp-∘∙ _ _ _)
    ∙ cong (-Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)))
           (sym (∘∙-assoc _ _ _)
          ∙ cong₂ _∘∙_ (·wh≡·whΣ _ _ _ _) refl)
    where
    ptLem : Square {A = join (Susp (typ B)) (Susp (typ A))}
                   (push north north ∙ sym (push north north))
                   (refl ∙ sym (push north north))
                   (push north north) refl
    ptLem = rCancel (push north north)
          ◁ (λ i j → push north north (~ j ∧ i))
          ▷ lUnit (sym (push north north))

    F1 F2 : Susp∙ (typ A) ⋀ Susp∙ (typ B)
       →  ((Path (join (fst (Susp∙ (typ B))) (fst (Susp∙ (typ A))))
                  (inl north) (inr north)))
    F1 a i = join-commFun (SuspSmash→Join (merid a i))
    F2 a = push north north
      ∙ cong (SuspSmash→Join
            ∘ fst ((-Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)))
                          (suspFun∙ ⋀comm→)))
             (merid a)

    F1≡F2 : F1 ≡ F2
    F1≡F2 = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
              λ x y →
              cong-∙∙ join-commFun _ _ _
            ∙ lUnit _
            ∙ cong₂ _∙_ (sym (rCancel _)) refl
            ∙ sym (assoc _ _ _)
            ∙ cong₂ _∙_ refl
                (sym (symDistr (cong SuspSmash→Join (merid (inr (y , x))))
                               (cong SuspSmash→Join (sym (merid (inl tt)))))
               ∙ cong sym (sym (cong-∙ SuspSmash→Join
                  (merid (inr (y , x)))
                  (sym (merid (inl tt)))))
               ∙ cong (congS SuspSmash→Join)
                  (cong sym
                    (sym (cong-∙ (fst (suspFun∙ ⋀comm→))
                      (merid (inr (x , y)))
                      (merid (inl tt) ⁻¹)))
                  ∙ rUnit _))

module _ {ℓ ℓ' ℓ'' ℓ'''} (A : Pointed ℓ) (B : Pointed ℓ')
  (C : Pointed ℓ'') {D : Pointed ℓ'''}
  (f : Susp∙ (Susp (typ A)) →∙ D)
  (g : Susp∙ (Susp (typ B)) →∙ D)
  (h : Susp∙ (Susp (typ C)) →∙ D)
  where
  -- Some abbreviations
  private
    whAB  = ·wh (Susp∙ (typ A)) (Susp∙ (typ B)) {D}
    whAC  = ·wh (Susp∙ (typ A)) (Susp∙ (typ C)) {D}

    whAB-C = ·wh ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ B))) (Susp∙ (typ C)) {D}
    whB-AC = ·wh (Susp∙ (typ B)) ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ C))) {D}

    Σ[A⋀B]→ΣA*ΣB = SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B))
    Σ[A⋀C]→ΣA*ΣC = SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ C))

  -- Main result
  private
    [f[gh]] = ·whΣ (Susp∙ (typ A)) (_ ⋀∙ _)
                  f
                  (·whΣ (Susp∙ (typ B)) (Susp∙ (typ C))
                    g h)

    [[fg]h] = ·whΣ (_ ⋀∙ _) (Susp∙ (typ C))
                  (·whΣ (Susp∙ (typ A)) (Susp∙ (typ B))
                    f g) h

    [g[fh]] = ·whΣ (Susp∙ (typ B)) (_ ⋀∙ _)
                  g
                  (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C))
                    f h)

  JacobiΣR : [f[gh]]
           ≡ ·Susp (Susp∙ (typ A) ⋀∙ (Susp∙ (typ B) ⋀∙ Susp∙ (typ C)))
                   ([[fg]h] ∘∙ suspFun∙ (Iso.fun SmashAssocIso))
                   ([g[fh]] ∘∙ suspFun∙ (Iso.inv SmashAssocIso
                                      ∘ (⋀comm→∙ ⋀→ idfun∙ _)
                                      ∘ Iso.fun SmashAssocIso))
  JacobiΣR = sym (·wh≡·whΣ _ _ _ _)
           ∙ cong₂ _∘∙_
               ((cong (·wh (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C)) f)
                       (sym (·wh≡·whΣ _ _ _ _)))
               ∙ JacobiR A B C f g h)
               refl
           ∙ fromSusp≅fromJoin⁻Pres+* _ _
           ∙ cong₂ (·Susp (Susp∙ (typ A) ⋀∙ (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))))
                   (∘∙-assoc _ _ _
                  ∙ (cong₂ _∘∙_ lem2 lem3
                  ∙ sym (∘∙-assoc _ _ _))
                  ∙ cong (_∘∙ suspFun∙ (fun SmashAssocIso))
                    (·wh≡·whΣ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B))
                              (Susp∙ (typ C))
                              (·whΣ (Susp∙ (typ A))
                              (Susp∙ (typ B)) f g) h))
                     (∘∙-assoc _ _ _
                   ∙ cong₂ _∘∙_ whB-AC≡whB-AC lem
                   ∙ sym (∘∙-assoc _ _ _)
                   ∙ cong (_∘∙ suspFun∙ compFun)
                          (·wh≡·whΣ (Susp∙ _) (_ ⋀∙ _) g
                            (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C)) f h)))
      where
      compFun = inv SmashAssocIso
              ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C)))
              ∘ fun SmashAssocIso

      whB-AC≡whB-AC : whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC)
         ≡ whB-AC g (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C)) f h)
      whB-AC≡whB-AC = cong (whB-AC g) (·wh≡·whΣ _ _ _ _)

      Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B] = fst (SuspSmash→Join∙ (Susp∙ (typ B))
                                 (Susp∙ (typ A) ⋀∙ Susp∙ (typ C)))

      lem : (correction₂ A B C f g h)
        ∘∙ SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))
        ≡ SuspSmash→Join∙ (Susp∙ (typ B)) (Susp∙ (typ A) ⋀∙ Susp∙ (typ C))
        ∘∙ suspFun∙ compFun
      lem = ΣPathP ((funExt (λ x
        → cong Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B] (cong (suspFun (inv SmashAssocIso) ∘
                          Join→SuspSmash
                         ∘ join→ ⋀comm→ (λ c → c)
                         ∘ SuspSmash→Join
                         ∘ suspFun (fun SmashAssocIso))
               (SuspSmash→Join→SuspSmash x ))
        ∙∙ cong Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B]
               (cong (suspFun (inv SmashAssocIso))
                 (SuspFun-Join→SuspSmash≡ ⋀comm→∙ (idfun∙ (Susp∙ (typ C)))
                   (SuspSmash→Join (suspFun (fun SmashAssocIso) x))))
        ∙∙ (cong Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B]
                 (funExt⁻ (sym (suspFunComp (inv SmashAssocIso)
                                            (⋀comm→∙ ⋀→ idfun∙ _)))
                   (Join→SuspSmash (SuspSmash→Join
                                     (suspFun (fun SmashAssocIso) x))))
         ∙∙ cong Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B] (cong (suspFun (inv SmashAssocIso
                                 ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C)))))
                          (SuspSmash→Join→SuspSmash
                            (suspFun (fun SmashAssocIso) x)))
         ∙∙ cong Σ[B⋀[A⋀C]]→ΣB*Σ[A⋀B]
                 (funExt⁻ (sym (suspFunComp (inv SmashAssocIso
                                 ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C))))
                                 (fun SmashAssocIso))) x))))
           , ((cong₂ _∙_ refl (cong₂ _∙_
                     (cong (congS (fst (Jcorrection₁⁻
                                        (Susp∙ (typ B)) (Susp∙ (typ A))
                                        (Susp∙ (typ C)))))
                           (sym (rUnit (sym (push (inl tt) north))))) refl
                              ∙ rCancel (push north (inl tt)))
                   ∙ sym (rUnit _))
            ◁ (flipSquare ((cong₃ _∙∙_∙∙_ refl refl (sym (rUnit _))
                         ∙ ∙∙lCancel (push north (inl tt)))
                        ◁ (λ j i → push north (inl tt) (~ j)))
             ▷ lUnit (sym (push north (inl tt))))))

      lem2 : whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h
        ≡ ·wh (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C))
              (·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g) h
      lem2 = cong₂ (·wh (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C)))
                   (·wh≡·whΣ _ _ _ _) refl

      lem3 : (correction₁ A B C f g h)
        ∘∙ SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))
        ≡ (SuspSmash→Join∙ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C))
        ∘∙ suspFun∙ (fun SmashAssocIso))
      lem3 =
        ΣPathP ((funExt (λ x
        → cong (SuspSmash→Join∙ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B))
                                 (Susp∙ (typ C)) .fst)
               (cong (suspFun (fun SmashAssocIso))
                     (SuspSmash→Join→SuspSmash x))))
               , compPathL→PathP (cong₂ _∙_ refl (sym (rUnit _) ∙ rCancel _)
               ∙ sym (rUnit _)
               ∙ lUnit _) )
