{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Generalised.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Loopspace

open Iso
open 3x3-span

-- Generalised Whitehead products
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
         (B : Pointed ℓ') {C : Pointed ℓ''}
         (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C) where

  ·wh : join∙ A B →∙ C
  ·wh = joinPinch∙ A B C
         (λ a b → (Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a)))

  -- alternative version using Suspension and smash
  private
    ·whΣ' : Susp∙ (Smash A B) →∙ C
    fst ·whΣ' north = pt C
    fst ·whΣ' south = pt C
    fst ·whΣ' (merid basel i) = pt C
    fst ·whΣ' (merid baser i) = pt C
    fst ·whΣ' (merid (proj a b) i) =
        (Ω→ f .fst (σ A a) ⁻¹
      ∙ (Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a))
       ∙ Ω→ g .fst (σ B b) ⁻¹) i
    fst ·whΣ' (merid (gluel a i₁) i) =
      (cong (λ p → (Ω→ f .fst (σ A a) ⁻¹
                  ∙ (p ∙ Ω→ f .fst (σ A a)) ∙ p ⁻¹))
            (Iso.inv ΩSuspAdjointIso g .snd)
     ∙ cong₂ _∙_ refl (sym (rUnit _) ∙ sym (lUnit _))
     ∙ lCancel _) i₁ i
    fst ·whΣ' (merid (gluer b i₁) i) =
      (cong (λ p → (p ⁻¹ ∙ (Ω→ g .fst (σ B b) ∙ p) ∙ Ω→ g .fst (σ B b) ⁻¹))
            (Iso.inv ΩSuspAdjointIso f .snd)
     ∙ (sym (lUnit _) ∙ cong₂ _∙_ (sym (rUnit _)) refl)
     ∙ lCancel _) i₁ i
    snd ·whΣ' = refl

  ·whΣ : Susp∙ (A ⋀ B) →∙ C
  fst ·whΣ = fst ·whΣ' ∘ suspFun ⋀→Smash
  snd ·whΣ = refl

  -- The two versions agree modulo the equivalence Σ(A ⋀ B) ≃ A * B
  ·wh≡·whΣ : ·wh ∘∙ (SuspSmash→Join∙ A B) ≡ ·whΣ
  ·wh≡·whΣ = ΣPathP (funExt lem , (sym (rUnit _)
    ∙ cong sym (cong₂ _∙_
       (Iso.inv ΩSuspAdjointIso g .snd)
       (Iso.inv ΩSuspAdjointIso f .snd)
      ∙ sym (rUnit refl))))
    where
    lem : (x : _) → ·wh .fst (Iso.fun (SmashJoinIso {A = A} {B = B}) x)
                  ≡ ·whΣ .fst x
    lem north = refl
    lem south = refl
    lem (merid a i) j = main j a i
      where
      main : Path ((A ⋀ B) → Ω C .fst)
                  (cong (·wh .fst ∘ SuspSmash→Join) ∘ merid)
                  (cong (fst ·whΣ') ∘ merid ∘ ⋀→Smash)
      main = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
        λ x y → cong-∙∙ (·wh .fst) (push x (pt B) ⁻¹) (push x y) (push (pt A) y ⁻¹)
              ∙ doubleCompPath≡compPath _ _ _
              ∙ cong₂ _∙_ (cong sym
                           (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso g .snd) refl
                          ∙ sym (lUnit _)))
                      (cong₂ _∙_ refl
                           (cong sym
                           (cong₂ _∙_ refl (Iso.inv ΩSuspAdjointIso f .snd)
                          ∙ sym (rUnit _))))

  -- Other direction
  ·whΣ≡·wh : ·wh ≡ ·whΣ ∘∙ Join→SuspSmash∙ A B
  ·whΣ≡·wh = sym (∘∙-idʳ _)
           ∙ cong (·wh ∘∙_)
                  (ΣPathP (funExt (λ x → sym (Iso.rightInv SmashJoinIso x))
                                , ((λ i j → push (pt A) (pt B) (i ∧ ~ j))
                                ▷ lUnit _)))
          ∙∙ sym (∘∙-assoc _ _ _)
          ∙∙ cong (_∘∙ Join→SuspSmash∙ A B) ·wh≡·whΣ

  --- PathP version
  open import Cubical.Foundations.Path
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Univalence
  PathP-·wh-·whΣ :
    PathP (λ i → isoToPath (fromSusp≅fromJoin {A = A} {B = B} {C = C}) i)
          ·whΣ ·wh
  PathP-·wh-·whΣ = post∘∙equiv-ua _ _ _ ·wh≡·whΣ
    where
    post∘∙equiv-ua : ∀ {ℓ ℓ'} {A B : Pointed ℓ} {C : Pointed ℓ'} (e : A ≃∙ B)
      (f : A →∙ C) (g : B →∙ C) → (g ∘∙ (fst (fst e) , snd e)) ≡ f
      → PathP (λ i → isoToPath (post∘∙equiv {C = C} e) i) f g
    post∘∙equiv-ua {B = B} {C = C} = Equiv∙J
      (λ A e → (f : A →∙ C) (g : B →∙ C) → (g ∘∙ (fst (fst e) , snd e)) ≡ f
      → PathP (λ i → isoToPath (post∘∙equiv {C = C} e) i) f g)
      λ e f g → toPathP (cong (λ P → transport P e)
                           (cong ua post∘∙equivId
                         ∙ uaIdEquiv)
              ∙ transportRefl _
              ∙ sym g
              ∙ ∘∙-idˡ f)
      where
      post∘∙equivId : ∀ {ℓ ℓ'} {A : Pointed ℓ} {C : Pointed ℓ'}
        → isoToEquiv (post∘∙equiv {C = C} (idEquiv∙ A)) ≡ idEquiv _
      post∘∙equivId = Σ≡Prop isPropIsEquiv
        (funExt λ f → ΣPathP (refl
          , (cong₂ _∙_ (cong (cong (fst f)) (sym (rUnit refl))) refl
                      ∙ sym (lUnit (snd f)))))

--- Other elementary properties and lemmas ---
  -- The generalised Whitehead product vanishes under suspension
  isConst-Susp·w : suspFun∙ (·wh .fst) ≡ const∙ _ _
  isConst-Susp·w = Susp·w∙
                 ∙ cong suspFun∙ (cong fst isConst-const*)
                 ∙ ΣPathP ((suspFunConst (pt C)) , refl)
    where
    const* : join∙ A B →∙ C
    fst const* (inl x) = pt C
    fst const* (inr x) = pt C
    fst const* (push a b i) =
      (Ω→ f .fst (σ A a) ∙ Ω→ g .fst (σ B b)) i
    snd const* = refl

    isConst-const* : const* ≡ const∙ _ _
    fst (isConst-const* i) (inl x) = Ω→ f .fst (σ A x) i
    fst (isConst-const* i) (inr x) = Ω→ g .fst (σ B x) (~ i)
    fst (isConst-const* i) (push a b j) =
      compPath-filler'' (Ω→ f .fst (σ A a)) (Ω→ g .fst (σ B b)) (~ i) j
    snd (isConst-const* i) j =
      (cong (Ω→ f .fst) (rCancel (merid (pt A))) ∙ Ω→ f .snd) j i

    Susp·w : suspFun (fst ·wh) ≡ suspFun (fst const*)
    Susp·w i north = north
    Susp·w i south = south
    Susp·w i (merid (inl x) j) = merid (pt C) j
    Susp·w i (merid (inr x) j) = merid (pt C) j
    Susp·w i (merid (push a b k) j) =
      hcomp (λ r →
        λ {(i = i0) → fill₁ k (~ r) j
         ; (i = i1) → fill₂ k (~ r) j
         ; (j = i0) → north
         ; (j = i1) → merid (pt C) r
         ; (k = i0) → compPath-filler (merid (snd C)) (merid (pt C) ⁻¹) (~ r) j
         ; (k = i1) → compPath-filler (merid (snd C)) (merid (pt C) ⁻¹) (~ r) j})
       (hcomp (λ r →
        λ {(i = i0) → doubleCompPath-filler
                         (sym (rCancel (merid (pt C))))
                         (λ k → fill₁ k i1)
                         (rCancel (merid (pt C))) (~ r) k j
         ; (i = i1) → doubleCompPath-filler
                         (sym (rCancel (merid (pt C))))
                         (λ k → fill₂ k i1)
                         (rCancel (merid (pt C))) (~ r) k j
         ; (j = i0) → north
         ; (j = i1) → north
         ; (k = i0) → rCancel (merid (pt C)) (~ r) j
         ; (k = i1) → rCancel (merid (pt C)) (~ r) j})
           (main i k j))
      where
      F : Ω C .fst → (Ω^ 2) (Susp∙ (fst C)) .fst
      F p = sym (rCancel (merid (pt C)))
         ∙∙ cong (σ C) p
         ∙∙ rCancel (merid (pt C))

      F-hom : (p q : _) → F (p ∙ q) ≡ F p ∙ F q
      F-hom p q =
          cong (sym (rCancel (merid (pt C)))
               ∙∙_∙∙ rCancel (merid (pt C)))
               (cong-∙ (σ C) p q)
        ∙ doubleCompPath≡compPath (sym (rCancel (merid (pt C)))) _ _
        ∙ cong (sym (rCancel (merid (pt C))) ∙_)
               (sym (assoc _ _ _))
        ∙ assoc _ _ _
        ∙ (λ i → (sym (rCancel (merid (pt C)))
                ∙ compPath-filler (cong (σ C) p) (rCancel (merid (pt C))) i)
                ∙ compPath-filler' (sym (rCancel (merid (pt C))))
                                   (cong (σ C) q ∙ rCancel (merid (pt C))) i)
        ∙ cong₂ _∙_ (sym (doubleCompPath≡compPath _ _ _))
                    (sym (doubleCompPath≡compPath _ _ _))

      main : F ((Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a)))
           ≡ F ((Ω→ f .fst (σ A a) ∙ Ω→ g .fst (σ B b)))
      main = F-hom (Ω→ g .fst (σ B b)) (Ω→ f .fst (σ A a))
           ∙ EH 0 _ _
           ∙ sym (F-hom (Ω→ f .fst (σ A a)) (Ω→ g .fst (σ B b)))

      fill₁ : (k : I) → _
      fill₁ k = compPath-filler
                (merid ((Ω→ g .fst (σ B b)
                       ∙ Ω→ f .fst (σ A a)) k))
                (merid (pt C) ⁻¹)

      fill₂ : (k : I) → _
      fill₂ k = compPath-filler
                (merid ((Ω→ f .fst (σ A a)
                       ∙ Ω→ g .fst (σ B b)) k))
                (merid (pt C) ⁻¹)

    Susp·w∙ : suspFun∙ (·wh .fst) ≡ suspFun∙ (fst const*)
    Susp·w∙ = ΣPathP (Susp·w , refl)

-- Action on the standard loop in Ω (join A B)
cong·wh-ℓ* : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
     (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C)
     (a : _) (b : _)
  → (cong (fst (·wh A B f g)) (ℓ* A B a b))
  ≡ ((Ω→ f .fst (σ A a) ⁻¹)
  ∙∙ (Ω→ g .fst (σ B b) ∙ Ω→ f .fst (σ A a))
  ∙∙ (Ω→ g .fst (σ B b) ⁻¹))
cong·wh-ℓ* {A = A} {B = B} f g a b =
    cong-∙ (fst (·wh A B f g)) _ _
  ∙ cong₂ _∙_ (cong₂ _∙_ gp fp
            ∙ sym (rUnit _))
            (cong-∙∙ (fst (·wh A B f g)) _ _ _
          ∙ cong₃ _∙∙_∙∙_
              (cong _⁻¹ (cong₂ _∙_ gp refl ∙ sym (lUnit _)))
              refl
              (cong _⁻¹ (cong₂ _∙_ refl fp ∙ sym (rUnit _))))
  ∙ sym (lUnit _)
  where
  fp = cong (Ω→ f .fst) (rCancel _) ∙ Ω→ f .snd
  gp = cong (Ω→ g .fst) (rCancel _) ∙ Ω→ g .snd
