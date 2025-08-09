{-# OPTIONS --safe #-}
module Cubical.Homotopy.WhiteheadProducts.Generalised.Smash.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Join
open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base

open Iso

-- Generalised Whitehead products
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') {C : Pointed ℓ''}
  (f : Susp∙ (typ A) →∙ C) (g : Susp∙ (typ B) →∙ C) where

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
            (inv (ΩSuspAdjointIso {A = B}) g .snd)
     ∙ cong₂ _∙_ refl (sym (rUnit _) ∙ sym (lUnit _))
     ∙ lCancel _) i₁ i
    fst ·whΣ' (merid (gluer b i₁) i) =
      (cong (λ p → (p ⁻¹ ∙ (Ω→ g .fst (σ B b) ∙ p) ∙ Ω→ g .fst (σ B b) ⁻¹))
            (inv (ΩSuspAdjointIso {A = A}) f .snd)
     ∙ (sym (lUnit _) ∙ cong₂ _∙_ (sym (rUnit _)) refl)
     ∙ lCancel _) i₁ i
    snd ·whΣ' = refl

  ·whΣ : Susp∙ (A ⋀ B) →∙ C
  fst ·whΣ = fst ·whΣ' ∘ suspFun ⋀→Smash
  snd ·whΣ = refl

  -- This version agrees with the join version modulo the
  -- equivalence Σ(A ⋀ B) ≃ A * B
  ·wh≡·whΣ : ·wh A B f g ∘∙ (SuspSmash→Join∙ A B) ≡ ·whΣ
  ·wh≡·whΣ = ΣPathP (funExt lem , (sym (rUnit _)
    ∙ cong sym (cong₂ _∙_
       (inv ΩSuspAdjointIso g .snd)
       (inv ΩSuspAdjointIso f .snd)
      ∙ sym (rUnit refl))))
    where
    lem : (x : _) → ·wh A B f g .fst (fun (SmashJoinIso {A = A} {B = B}) x)
                  ≡ ·whΣ .fst x
    lem north = refl
    lem south = refl
    lem (merid a i) j = main j a i
      where
      main : Path ((A ⋀ B) → Ω C .fst)
                  (cong (·wh A B f g .fst ∘ SuspSmash→Join) ∘ merid)
                  (cong (fst ·whΣ') ∘ merid ∘ ⋀→Smash)
      main = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
        λ x y → cong-∙∙ (·wh A B f g .fst)
                         (push x (pt B) ⁻¹) (push x y) (push (pt A) y ⁻¹)
              ∙ doubleCompPath≡compPath _ _ _
              ∙ cong₂ _∙_ (cong sym
                           (cong₂ _∙_ (inv ΩSuspAdjointIso g .snd) refl
                          ∙ sym (lUnit _)))
                      (cong₂ _∙_ refl
                           (cong sym
                           (cong₂ _∙_ refl (inv ΩSuspAdjointIso f .snd)
                          ∙ sym (rUnit _))))

  -- Other direction
  ·whΣ≡·wh : ·wh A B f g ≡ ·whΣ ∘∙ Join→SuspSmash∙ A B
  ·whΣ≡·wh =
       sym (∘∙-idʳ _)
     ∙ cong (·wh A B f g ∘∙_)
            (ΣPathP (funExt (λ x →
              sym (rightInv (SmashJoinIso {A = A} {B = B}) x))
            , ((λ i j → push (pt A) (pt B) (i ∧ ~ j))
            ▷ lUnit _)))
    ∙∙ sym (∘∙-assoc (·wh A B f g) (SuspSmash→Join∙ A B) (Join→SuspSmash∙ A B))
    ∙∙ cong (_∘∙ Join→SuspSmash∙ A B) ·wh≡·whΣ

  --- PathP version
  PathP-·wh-·whΣ :
    PathP (λ i → isoToPath (fromSusp≅fromJoin {A = A} {B = B} {C = C}) i)
          ·whΣ (·wh A B f g)
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
