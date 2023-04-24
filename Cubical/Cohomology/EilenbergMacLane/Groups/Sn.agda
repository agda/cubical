{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Sn where

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.EilenbergMacLane1 hiding (elimProp ; elimSet)
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 renaming (rec to S¹fun)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

SⁿFun : (n : ℕ) (a : A) → (S₊ (suc n) → a ≡ a)
  → S₊ (suc (suc n)) → A
SⁿFun n a f north = a
SⁿFun n a f south = a
SⁿFun n a f (merid a₁ i) = f a₁ i

characSⁿFun : (n : ℕ) (f : S₊ (suc (suc n)) → A)
  → SⁿFun n (f north) (λ x → cong f (toSusp (S₊∙ (suc n)) x)) ≡ f
characSⁿFun n f =
  funExt λ { north → refl
           ; south → cong f (merid (ptSn (suc n)))
           ; (merid a i) j
             → f (compPath-filler (merid a)
                   (sym (merid (ptSn (suc n)))) (~ j) i)}

characS¹Fun : (f : S¹ → A)
  → S¹fun (f base) (cong f loop) ≡ f
characS¹Fun f =
  funExt λ { base → refl
           ; (loop i) → refl }

Sⁿ-connElim : (n : ℕ) {B : (S₊ (suc (suc n)) → A) → Type ℓ'}
  → isConnected 2 A
  → ((x : _) → isProp (B x))
  → (a : A)
  → ((p : S₊ (suc n) → a ≡ a) → B (SⁿFun n a p))
  → (x : _) → B x
Sⁿ-connElim n {B = B} conA pr a ind f =
  subst B (characSⁿFun n f)
    (TR.rec (pr _)
      (λ p → J (λ a p → (p₁ : S₊ (suc n) → a ≡ a) → B (SⁿFun n a p₁))
               ind (sym p)
               (λ x → cong f (toSusp (S₊∙ (suc n)) x)))
      (isConnectedPath 1 conA (f north) a .fst))

S¹-connElim : {B : (S¹ → A) → Type ℓ'}
  → isConnected 2 A
  → ((x : _) → isProp (B x))
  → (a : A)
  → ((p : a ≡ a) → B (S¹fun a p))
  → (x : _) → B x
S¹-connElim {B = B} conA pr a ind f =
  subst B (characS¹Fun f)
    (TR.rec (pr _)
      (λ p → J (λ a p → (q : a ≡ a) → B (S¹fun a q)) ind
        (sym p) (cong f loop))
      (isConnectedPath 1 conA (f base) a .fst))

module _ (G : AbGroup ℓ) where
  open AbGroupStr (snd G)
  H¹S¹→G : coHom 1 G S¹ → fst G
  H¹S¹→G = ST.rec is-set λ f → ΩEM+1→EM-gen 0 (f base) (cong f loop)

  G→H¹S¹ : fst G → coHom 1 G S¹
  G→H¹S¹ g = ∣ S¹fun (0ₖ 1) (emloop g) ∣₂

  H¹[S¹,G]≅G : AbGroupEquiv (coHomGr 1 G S¹) G
  fst H¹[S¹,G]≅G = isoToEquiv is
    where
    is : Iso _ _
    Iso.fun is = H¹S¹→G
    Iso.inv is = G→H¹S¹
    Iso.rightInv is = Iso.leftInv (Iso-EM-ΩEM+1 0)
    Iso.leftInv is =
      ST.elim (λ _ → isSetPathImplicit)
        (S¹-connElim (isConnectedEM 1) (λ _ → squash₂ _ _)
          embase
          λ p → cong ∣_∣₂ (cong (S¹fun embase) (Iso.rightInv (Iso-EM-ΩEM+1 0) p)))
  snd H¹[S¹,G]≅G =
    isGroupHomInv ((invEquiv (fst H¹[S¹,G]≅G))
     , makeIsGroupHom λ x y → cong ∣_∣₂
       (funExt λ { base → refl
                ; (loop i) j → (emloop-comp _ x y
                               ∙ sym (cong₂+₁ (emloop x) (emloop y))) j i}))

  HⁿSⁿ↓ : (n : ℕ) → coHom (suc (suc n)) G (S₊ (suc (suc n)))
                   → coHom (suc n) G (S₊ (suc n))
  HⁿSⁿ↓ n = ST.map λ f x → ΩEM+1→EM-gen (suc n) _ (cong f (toSusp (S₊∙ (suc n)) x))

  private
    liftMap : (n : ℕ) (f : S₊ (suc n) → EM G (suc n))
           → S₊ (suc (suc n)) → EM G (suc (suc n))
    liftMap n f = SⁿFun n (0ₖ _) (EM→ΩEM+1 (suc n) ∘ f)

  HⁿSⁿ↑ : (n : ℕ) → coHom (suc n) G (S₊ (suc n))
                  → coHom (suc (suc n)) G (S₊ (suc (suc n)))
  HⁿSⁿ↑ n = ST.map (liftMap n)

  Hⁿ[Sⁿ,G]≅Hⁿ⁺¹[Sⁿ⁺¹,G] : (n : ℕ)
    → AbGroupEquiv (coHomGr (suc n) G (S₊ (suc n)))
                    (coHomGr (suc (suc n)) G (S₊ (suc (suc n))))
  fst (Hⁿ[Sⁿ,G]≅Hⁿ⁺¹[Sⁿ⁺¹,G] n) = isoToEquiv is
    where
    is : Iso _ _
    Iso.fun is = HⁿSⁿ↑ n
    Iso.inv is = HⁿSⁿ↓ n
    Iso.rightInv is =
      ST.elim (λ _ → isSetPathImplicit)
        (Sⁿ-connElim n (isConnectedSubtr 2 (suc n)
          (subst (λ x → isConnected x (EM G (suc (suc n))))
          (cong suc (+-comm 2 n)) (isConnectedEM (suc (suc n)))))
          (λ _ → squash₂ _ _)
          (0ₖ _)
          λ p → TR.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
            (λ q → cong ∣_∣₂ (cong (SⁿFun n (0ₖ (suc (suc n))))
                  (funExt (λ x
                    → cong (Iso.fun (Iso-EM-ΩEM+1 (suc n))
                             ∘ Iso.inv (Iso-EM-ΩEM+1 (suc n)))
                            (cong-∙ (SⁿFun n (0ₖ (suc (suc n))) p)
                                    (merid x) (sym (merid (ptSn (suc n))))
                            ∙ cong (p x ∙_) (cong sym q)
                            ∙ sym (rUnit (p x)))
                      ∙ Iso.rightInv (Iso-EM-ΩEM+1 (suc n)) (p x)))))
                      (isConnectedPath (suc n)
                        (isConnectedPath (suc (suc n))
                          (isConnectedEM (suc (suc n))) _ _)
                           (p (ptSn _)) refl .fst))
    Iso.leftInv is = ST.elim (λ _ → isSetPathImplicit)
        λ f → TR.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
          (λ q → cong ∣_∣₂ (funExt λ x
          → cong (ΩEM+1→EM (suc n))
                   (cong-∙ (liftMap n f) (merid x) (sym (merid (ptSn _)))
                 ∙ cong (cong (liftMap n f) (merid x) ∙_)
                        (cong sym (cong (EM→ΩEM+1 (suc n)) q
                                ∙ EM→ΩEM+1-0ₖ (suc n)))
                 ∙ sym (rUnit _))
                 ∙ Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) (f x)))
                 (isConnectedPath (suc n)
                   (isConnectedEM (suc n))
                   (f (ptSn (suc n))) (0ₖ (suc n)) .fst)
  snd (Hⁿ[Sⁿ,G]≅Hⁿ⁺¹[Sⁿ⁺¹,G] n) =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isSetPathImplicit)
        λ f g → cong ∣_∣₂
          (funExt λ { north → refl
                    ; south → refl
                    ; (merid a i) j
                    → (EM→ΩEM+1-hom (suc n) (f a) (g a)
                     ∙ sym (cong₂+₂ _ (EM→ΩEM+1 (suc n) (f a))
                                      (EM→ΩEM+1 (suc n) (g a)))) j i}))

  Hⁿ[Sⁿ,G]≅G : (n : ℕ) → AbGroupEquiv (coHomGr (suc n) G (S₊ (suc n))) G
  Hⁿ[Sⁿ,G]≅G zero = H¹[S¹,G]≅G
  Hⁿ[Sⁿ,G]≅G (suc n) =
    compGroupEquiv (invGroupEquiv (Hⁿ[Sⁿ,G]≅Hⁿ⁺¹[Sⁿ⁺¹,G] n))
                   (Hⁿ[Sⁿ,G]≅G n)

  isContr-Hᵐ⁺ⁿ[Sⁿ,G] : (n m : ℕ)
    → isContr (coHom ((suc m) +ℕ suc n) G (S₊ (suc n)))
  fst (isContr-Hᵐ⁺ⁿ[Sⁿ,G] zero m) = 0ₕ _
  snd (isContr-Hᵐ⁺ⁿ[Sⁿ,G] zero m) =
    ST.elim (λ _ → isSetPathImplicit)
           (S¹-connElim
            (isConnectedSubtr 2 (suc m)
             (subst (λ x → isConnected x (EM G (suc (m +ℕ 1))))
             (cong suc (sym (+-suc m 1)))
             (isConnectedEM (suc (m +ℕ 1)))))
             (λ _ → squash₂ _ _)
             (0ₖ _)
             λ p → TR.rec (isOfHLevelPlus {n = 1} m (squash₂ _ _))
               (λ q → cong ∣_∣₂ (sym (characS¹Fun (λ _ → 0ₖ _))
                              ∙ cong (S¹fun (0ₖ (suc (m +ℕ 1)))) q))
               (isConnectedPath (m +ℕ 1)
                 (isConnectedPath (suc (m +ℕ 1))
                   (isConnectedEM (suc (m +ℕ 1))) _ _) refl p .fst))
  fst (isContr-Hᵐ⁺ⁿ[Sⁿ,G] (suc n) m) = 0ₕ _
  snd (isContr-Hᵐ⁺ⁿ[Sⁿ,G] (suc n) m) =
    ST.elim (λ _ → isSetPathImplicit)
           (Sⁿ-connElim n
             (isConnectedSubtr 2 (suc (suc m) +ℕ n)
               (subst (λ x → isConnected x (EM G (suc (m +ℕ suc (suc n)))))
                      (cong (suc ∘ suc)
                        (cong (m +ℕ_) (+-comm 2 n) ∙ +-assoc m n 2))
                      (isConnectedEM (suc (m +ℕ suc (suc n))))))
             (λ _ → squash₂ _ _)
             (0ₖ _)
             λ p → PT.rec (squash₂ _ _)
               (λ q → cong ∣_∣₂ (sym (characSⁿFun n (λ _ → 0ₖ _))
                          ∙ cong (SⁿFun n (0ₖ (suc (m +ℕ suc (suc n))))) q))
                 (Iso.fun PathIdTrunc₀Iso
                   (isContr→isProp
                     (subst (λ A → isContr ∥ (S₊ (suc n) → A) ∥₂)
                            (cong (EM G) (sym (+-suc m (suc n)))
                            ∙ isoToPath (Iso-EM-ΩEM+1 _))
                            (isContr-Hᵐ⁺ⁿ[Sⁿ,G] n m))
                     _ _)))

  Hᵐ⁺ⁿ[Sⁿ,G]≅0 : (n m : ℕ)
    → AbGroupEquiv (coHomGr ((suc m) +ℕ suc n) G (S₊ (suc n)))
                    (trivialAbGroup {ℓ-zero})
  fst (Hᵐ⁺ⁿ[Sⁿ,G]≅0 zero m) =
    isoToEquiv (isContr→Iso (isContr-Hᵐ⁺ⁿ[Sⁿ,G] 0 m) isContrUnit*)
  snd (Hᵐ⁺ⁿ[Sⁿ,G]≅0 zero m) =
    makeIsGroupHom λ _ _ → refl
  fst (Hᵐ⁺ⁿ[Sⁿ,G]≅0 (suc n) m) =
    isoToEquiv
      (isContr→Iso (isContr-Hᵐ⁺ⁿ[Sⁿ,G] (suc n) m) isContrUnit*)
  snd (Hᵐ⁺ⁿ[Sⁿ,G]≅0 (suc n) m) = makeIsGroupHom λ _ _ → refl

  Hⁿ[Sᵐ⁺ⁿ,G]≅0 : (n m : ℕ)
    → AbGroupEquiv (coHomGr (suc n) G (S₊ ((suc m) +ℕ suc n)))
                    (trivialAbGroup {ℓ-zero})
  fst (Hⁿ[Sᵐ⁺ⁿ,G]≅0 zero m) =
    isoToEquiv
      (isContr→Iso
        ((0ₕ _)
        , (ST.elim (λ _ → isSetPathImplicit)
           (subst (λ x → (a : S₊ x → EM G 1) → 0ₕ 1 ≡ ∣ a ∣₂)
                  (cong suc (+-comm 1 m))
                  λ f → TR.rec (squash₂ _ _)
                  (λ q → cong ∣_∣₂ (funExt (sphereElim (suc m)
                    (λ _ → isOfHLevelPath' (suc (suc zero +ℕ m))
                      (isOfHLevelPlus' {n = m} 3 (hLevelEM _ 1)) _ _) q)))
                      (isConnectedPath 1 (isConnectedEM 1) embase (f north) .fst))))
        isContrUnit*)
  snd (Hⁿ[Sᵐ⁺ⁿ,G]≅0 zero m) =
    makeIsGroupHom λ _ _ → refl
  fst (Hⁿ[Sᵐ⁺ⁿ,G]≅0 (suc n) m) =
    isoToEquiv
      (isContr→Iso
        ((0ₕ _)
       , ST.elim (λ _ → isSetPathImplicit)
          (subst (λ x → (a : S₊ x → EM G (suc (suc n)))
                      → 0ₕ (suc (suc n)) ≡ ∣ a ∣₂)
                 (cong suc (cong suc (sym (+-suc m n))
                          ∙ sym (+-suc m (suc n))))
                 λ f →
                   TR.rec (isProp→isOfHLevelSuc (suc n) (squash₂ _ _))
                          (λ q → cong ∣_∣₂
                           (funExt (sphereElim _
                             (λ s → isOfHLevelPath' (suc (suc (suc (m +ℕ n))))
                               (subst (λ x → isOfHLevel x (EM G (suc (suc n))))
                                 (+-assoc m 4 n ∙ cong (_+ℕ n) (+-comm m 4))
                                 (isOfHLevelPlus {n = 4 +ℕ n} m
                                   (hLevelEM G (suc (suc n))))) _ _)
                             q)))
                          (isConnectedPath _
                          (isConnectedEM (suc (suc n))) (0ₖ _) (f north) .fst)))
        isContrUnit*)
  snd (Hⁿ[Sᵐ⁺ⁿ,G]≅0 (suc n) m) = makeIsGroupHom λ _ _ → refl
