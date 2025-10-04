{-# OPTIONS --lossy-unification #-}
-- Other lemmas about homotopy groups
module Cubical.Homotopy.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Abelianization.Properties

private
  variable
    ℓ : Level

-- Interaction of iterated inversion with other sphere inversions
-π^≡iter-Π : {k : ℕ} {A : Pointed ℓ} (n : ℕ)
  → (x : π' (suc k) A) → -π^ n x ≡ ST.map (iter n -Π) x
-π^≡iter-Π zero = ST.elim (λ _ → isSetPathImplicit) λ _ → refl
-π^≡iter-Π {k = k} (suc n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong (-π^ 1) (-π^≡iter-Π {k = k} n ∣ f ∣₂)

-Π≡∘-S : {k : ℕ} {A : Pointed ℓ} (f : S₊∙ (suc k) →∙ A)
  → -Π f ≡ (f ∘∙ (invSphere , invSpherePt))
-Π≡∘-S {k = zero} f =
  ΣPathP ((funExt (λ { base → refl
                    ; (loop i) → refl}))
        , lUnit (snd f))
-Π≡∘-S {k = suc k} f =
  ΣPathP ((funExt (λ { north → cong (fst f) (merid (ptSn (suc k)))
                     ; south → refl
                     ; (merid a i) j
                  → fst f (compPath-filler (merid a)
                            (sym (merid (ptSn (suc k)))) (~ j) (~ i))}))
        , (compPath-filler'
             (cong (fst f) (sym (merid (ptSn (suc k)))))
             (snd f)))

iter-Π≡∘-S^ : {k : ℕ} {A : Pointed ℓ} (n : ℕ) (f : S₊∙ (suc k) →∙ A)
  → iter n -Π f ≡ (f ∘∙ (-S^ n , -S^pt n))
iter-Π≡∘-S^ zero f = ΣPathP (refl , lUnit (snd f))
iter-Π≡∘-S^ {k = k} {A} (suc n) f =
  cong -Π (iter-Π≡∘-S^ {k = k} {A} n f)
  ∙ -Π≡∘-S (f ∘∙ (-S^ n , -S^pt n))
  ∙ ∘∙-assoc f (-S^ n , -S^pt n) (invSphere , invSpherePt) --
  ∙ cong (f ∘∙_)
    (ΣPathP ((funExt (λ x → sym (invSphere-S^ n x)))
           , (lem k n)))
  where
  fl : (k : ℕ) (n : ℕ)
    → Σ[ p ∈ invSphere (invSphere (ptSn (suc k))) ≡ ptSn (suc k) ]
    ((Square (cong invSphere (sym (invSpherePt {k = k})) )
            refl invSpherePt p)
    × Square (cong (invSphere ∘ invSphere) (-S^pt {k = k} n))
             (cong invSphere (cong invSphere (-S^pt n) ∙ invSpherePt)
                            ∙ invSpherePt)
             refl
             p)
  fl zero n .fst = refl
  fl (suc k) n .fst = refl
  fl zero n .snd = refl
    , (cong (congS invLooper) (rUnit (cong invLooper (-S^pt n))) ∙ rUnit _)
  fl (suc k) n .snd .fst i j = merid (ptSn (suc k)) (~ i ∧ ~ j)
  fl (suc k) n .snd .snd i j =
    hcomp (λ r → λ {(i = i0) → invSusp (invSusp (-S^pt n j))
                   ; (j = i0) → invSusp (invSusp (iter n invSusp north))
                   ; (j = i1) → merid (ptSn (suc k)) (~ r ∧ i)})
           (invSusp (compPath-filler (cong invSusp (-S^pt n))
                      (sym (merid (ptSn (suc k)))) i j))

  lem : (k : ℕ) (n : ℕ)
    → Square (cong (-S^ n) (invSpherePt {k = k}) ∙ -S^pt n)
              (-S^pt (suc n))
              (sym (invSphere-S^ n (ptSn (suc k)))) refl
  lem k zero = sym (rUnit _) ∙ lUnit _
  lem k (suc n) i j =
    hcomp (λ r → λ {(i = i0) → (cong (-S^ (suc n)) (invSpherePt {k = k})
                              ∙ compPath-filler (cong invSphere (-S^pt n))
                                                      invSpherePt r) j
                   ; (i = i1) → fl k n .snd .snd r j
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → fl k n .snd .fst r i
                   })
     (hcomp (λ r → λ {(i = i0) → cong-∙ invSphere
                                         (cong (-S^ n) (invSpherePt {k = k}))
                                         (-S^pt n) r j
                   ; (i = i1) → invSphere (doubleCompPath-filler refl
                                 (cong invSphere (-S^pt n)) invSpherePt (~ r) j)
                   ; (j = i0) → invSphere-S^ (suc n) (ptSn (suc k)) (~ i)
                   ; (j = i1) → invSphere (invSpherePt (~ r ∨ ~ i))})
          (invSphere (lem k n i j)))

connectedFun→πEquiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → GroupEquiv (πGr n A) (πGr n B)
connectedFun→πEquiv {ℓ = ℓ}  {A = A} {B = B} n f conf =
  (πHom n f .fst
  , subst isEquiv (funExt (ST.elim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (πA≃πB .snd))
  , πHom n f .snd
  where
  lem : (n : ℕ) → suc (suc n) ∸ n ≡ 2
  lem zero = refl
  lem (suc n) = lem n

  connΩ^→f : isConnectedFun 2 (fst (Ω^→ (suc n) f))
  connΩ^→f = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc (suc n)) (suc n) f conf)

  πA≃πB : π (suc n) A ≃ π (suc n) B
  πA≃πB = compEquiv setTrunc≃Trunc2
         (compEquiv (connectedTruncEquiv 2
                     (fst (Ω^→ (suc n) f)) connΩ^→f)
          (invEquiv setTrunc≃Trunc2))

connectedFun→π'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) = π'∘∙Hom n f .fst
snd (fst (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) =
  transport (λ i → isEquiv (GroupHomπ≅π'PathP-hom n f i .fst))
            (connectedFun→πEquiv n f conf .fst .snd)
snd (connectedFun→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf) = π'∘∙Hom n f .snd

connected→Abπ'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 + n) (fst f)
  → AbGroupEquiv (AbelianizationAbGroup (π'Gr n A)) (AbelianizationAbGroup (π'Gr n B))
connected→Abπ'Equiv n f isc = AbelianizationEquiv (connectedFun→π'Equiv n f isc)

connectedFun→πSurj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 + n) (fst f)
  → isSurjective {G = πGr n A} {H = πGr n B} (πHom n f)
connectedFun→πSurj {ℓ = ℓ}  {A = A} {B = B} n f conf =
  ST.elim (λ _ → isProp→isSet squash₁)
    λ p → TR.rec squash₁ (λ {(q , r) → ∣ ∣ q ∣₂ , (cong ∣_∣₂ r) ∣₁})
                 (connΩ^→f p .fst)
  where
  lem : (n : ℕ) → suc n ∸ n ≡ 1
  lem zero = refl
  lem (suc n) = lem n

  connΩ^→f : isConnectedFun 1 (fst (Ω^→ (suc n) f))
  connΩ^→f = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
                    (lem n)
                    (isConnectedΩ^→ (suc n) (suc n) f conf)

connectedFun→π'Surj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 + n) (fst f)
  → isSurjective (π'∘∙Hom n f)
connectedFun→π'Surj n f conf =
  transport (λ i → isSurjective (GroupHomπ≅π'PathP-hom n f i))
            (connectedFun→πSurj n f conf)
