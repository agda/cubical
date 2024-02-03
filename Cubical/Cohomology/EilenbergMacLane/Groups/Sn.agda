{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Sn where

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.EilenbergMacLane1 hiding (elimProp ; elimSet)
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 renaming (rec to S¹fun)

open RingStr renaming (_+_ to _+r_)
open PlusBis

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
  open AbGroupStr (snd G) renaming (is-set to is-setG)
  H¹S¹→G : coHom 1 G S¹ → fst G
  H¹S¹→G = ST.rec is-setG λ f → ΩEM+1→EM-gen 0 (f base) (cong f loop)

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
  open import Cubical.Data.Sum as ⊎
  open import Cubical.Data.Empty as ⊥
  open import Cubical.Relation.Nullary
  open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

  H⁰[Sⁿ,G]≅G : (n : ℕ) → AbGroupEquiv (coHomGr 0 G (S₊ (suc n))) G
  H⁰[Sⁿ,G]≅G n = H⁰conn
      (∣ ptSn (suc n) ∣ₕ
    , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
        (sphereElim n (λ _ → isProp→isOfHLevelSuc n (isOfHLevelTrunc 2 _ _))
          refl))) G

  Hⁿ[Sᵐ,G]Full : (n m : ℕ)
    → (((n ≡ 0) ⊎ (n ≡ suc m))
          → AbGroupEquiv (coHomGr n G (S₊ (suc m))) G)
     × ((¬ n ≡ 0) × (¬ (n ≡ suc m))
           → AbGroupEquiv (coHomGr n G (S₊ (suc m))) (trivialAbGroup {ℓ-zero}))
  fst (Hⁿ[Sᵐ,G]Full zero m) _ = H⁰[Sⁿ,G]≅G m
  snd (Hⁿ[Sᵐ,G]Full zero  m) p = ⊥.rec (fst p refl)
  Hⁿ[Sᵐ,G]Full  (suc n) m with (n ≟ m)
  ... | lt x = (λ { (inl x) → ⊥.rec (snotz x)
                  ; (inr p) → ⊥.rec (¬m<m (subst (n <_) (sym (cong predℕ p)) x))})
             , λ _ → subst (λ m → AbGroupEquiv (coHomGr (suc n) G (S₊ m))
                                                 (trivialAbGroup {ℓ-zero}))
                            (cong suc (snd x))
                            (Hⁿ[Sᵐ⁺ⁿ,G]≅0 n (fst x))
  ... | eq x =
      (λ { (inl x) → ⊥.rec (snotz x)
         ; (inr x) → subst (λ m → AbGroupEquiv (coHomGr (suc n) G (S₊ m)) G)
                            x
                            (Hⁿ[Sⁿ,G]≅G n)})
    , (λ p → ⊥.rec (p .snd (cong suc x)))
  ... | gt x = (λ { (inl x) → ⊥.rec (snotz x)
                  ; (inr p) → ⊥.rec (¬m<m (subst (m <_) (cong predℕ p) x))})
             , λ _ → subst (λ n → AbGroupEquiv (coHomGr n G (S₊ (suc m)))
                                                 (trivialAbGroup {ℓ-zero}))
                            (cong suc (snd x))
                            (Hᵐ⁺ⁿ[Sⁿ,G]≅0 m (fst x))

-- In fact, the above induces an equivalence (S₊∙ n →∙ EM∙ G n) ≃ G
isSet-Sn→∙EM : (G : AbGroup ℓ) (n : ℕ) → isSet (S₊∙ n →∙ EM∙ G n)
isSet-Sn→∙EM G n =
  subst isSet (sym (help n)
            ∙ isoToPath (invIso (IsoSphereMapΩ n)))
    (AbGroupStr.is-set (snd G))
  where
  help : (n : ℕ) → fst ((Ω^ n) (EM∙ G n)) ≡ fst G
  help zero = refl
  help (suc n) =
      cong fst (flipΩPath n)
    ∙ cong (fst ∘ (Ω^ n))
       (ua∙ (isoToEquiv (invIso (Iso-EM-ΩEM+1 n)))
            (ΩEM+1→EM-refl n))
    ∙ help n

-- The equivalence (Sⁿ →∙ K(G,n)) ≃ G
HⁿSⁿ-raw≃G : (G : AbGroup ℓ) (n : ℕ)
  → (S₊∙ n →∙ EM∙ G n) ≃ (fst G)
HⁿSⁿ-raw≃G G zero =
  isoToEquiv
    (iso (λ f → fst f false)
         (λ g → (λ {true → _ ; false → g}) , refl)
         (λ g → refl)
         λ g → Σ≡Prop (λ _ → AbGroupStr.is-set (snd G) _ _)
                       (funExt λ { false → refl ; true → sym (snd g)}))
HⁿSⁿ-raw≃G G (suc n) =
    compEquiv
    (invEquiv
      (compEquiv (fst (coHom≅coHomRed n G (S₊∙ (suc n))))
      (isoToEquiv (setTruncIdempotentIso (isSet-Sn→∙EM G (suc n))))))
    (fst (Hⁿ[Sⁿ,G]≅G G n))

-- generator of HⁿSⁿ ≃ (Sⁿ →∙ K(G,n))
gen-HⁿSⁿ-raw : (R : Ring ℓ) (n : ℕ)
  → (S₊∙ n →∙ EM∙ (Ring→AbGroup  R) n)
fst (gen-HⁿSⁿ-raw R zero) false = 1r (snd R)
fst (gen-HⁿSⁿ-raw R zero) true = 0ₖ {G = Ring→AbGroup R} 0
snd (gen-HⁿSⁿ-raw R zero) = refl
fst (gen-HⁿSⁿ-raw R (suc zero)) base = 0ₖ 1
fst (gen-HⁿSⁿ-raw R (suc zero)) (loop i) = emloop (1r (snd R)) i
fst (gen-HⁿSⁿ-raw R (suc (suc n))) north = 0ₖ (2 +ℕ n)
fst (gen-HⁿSⁿ-raw R (suc (suc n))) south = 0ₖ (2 +ℕ n)
fst (gen-HⁿSⁿ-raw R (suc (suc n))) (merid a i) =
  EM→ΩEM+1 (suc n) (gen-HⁿSⁿ-raw R (suc n) .fst a) i
snd (gen-HⁿSⁿ-raw R (suc zero)) = refl
snd (gen-HⁿSⁿ-raw R (suc (suc n))) = refl

-- looping map (Sⁿ⁺¹ →∙ K(G,n+1)) → (Sⁿ →∙ K(G,n))
desuspHⁿSⁿ : (G : AbGroup ℓ) (n : ℕ)
  → (S₊∙ (suc n) →∙ EM∙ G (suc n))
  → (S₊∙ n →∙ EM∙ G n)
fst (desuspHⁿSⁿ G zero f) =
  λ {false → ΩEM+1→EM-gen 0 _ (cong (fst f) loop)
   ; true → AbGroupStr.0g (snd G)}
fst (desuspHⁿSⁿ G (suc n) f) x =
  ΩEM+1→EM-gen (suc n) _
    (cong (fst f) (toSusp (S₊∙ (suc n)) x))
snd (desuspHⁿSⁿ G zero f) = refl
snd (desuspHⁿSⁿ G (suc n) f) =
    cong (ΩEM+1→EM-gen (suc n) _)
      (cong (cong (fst f)) (rCancel (merid (ptSn (suc n)))))
  ∙ (λ i → ΩEM+1→EM-gen (suc n) _ (refl {x = snd f i}))
  ∙ ΩEM+1→EM-refl (suc n)

-- The equivalence respects desuspHⁿSⁿ
HⁿSⁿ-raw≃G-ind : (G : AbGroup ℓ) (n : ℕ)
  → (f : S₊∙ (suc n) →∙ EM∙ G (suc n))
  → HⁿSⁿ-raw≃G G (suc n) .fst f
   ≡ HⁿSⁿ-raw≃G G n .fst (desuspHⁿSⁿ G n f)
HⁿSⁿ-raw≃G-ind G zero f = refl
HⁿSⁿ-raw≃G-ind G (suc n) f = refl

-- The equivalence preserves the unit
gen-HⁿSⁿ-raw↦1 : (R : Ring ℓ) (n : ℕ)
  → HⁿSⁿ-raw≃G (Ring→AbGroup R) n .fst (gen-HⁿSⁿ-raw R n) ≡ 1r (snd R)
gen-HⁿSⁿ-raw↦1 R zero = refl
gen-HⁿSⁿ-raw↦1 R (suc zero) = transportRefl _
                        ∙ +IdL (snd R) (1r (snd R))
gen-HⁿSⁿ-raw↦1 R (suc (suc n)) =
  cong (fst (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup R) n) .fst)
      (cong ∣_∣₂ (funExt λ x
        → (cong (ΩEM+1→EM (suc n))
             (cong-∙ (fst (gen-HⁿSⁿ-raw R (suc (suc n))))
               (merid x) (sym (merid (ptSn (suc n)))))
        ∙ ΩEM+1→EM-hom (suc n) _ _)
        ∙ cong₂ _+ₖ_
           (Iso.leftInv (Iso-EM-ΩEM+1 (suc n))
           (gen-HⁿSⁿ-raw R (suc n) .fst x))
            (((λ i → ΩEM+1→EM-sym (suc n)
              (EM→ΩEM+1 (suc n) (snd (gen-HⁿSⁿ-raw R (suc n)) i)) i)
            ∙ cong -ₖ_ (Iso.leftInv (Iso-EM-ΩEM+1 (suc n)) (0ₖ (suc n)))
            ∙ -0ₖ (suc n)))
        ∙ rUnitₖ (suc n) _))
  ∙ gen-HⁿSⁿ-raw↦1 R (suc n)

-- explicit characterisation of the inverse of the equivalence
-- in terms of ⌣ₖ.
HⁿSⁿ-raw≃G-inv : (R : Ring ℓ) (n : ℕ)
  → fst R → (S₊∙ n →∙ EM∙ (Ring→AbGroup R) n)
fst (HⁿSⁿ-raw≃G-inv R n r) x =
  subst (EM (Ring→AbGroup R)) (+'-comm n 0)
    (_⌣ₖ_ {n = n} {m = 0} (fst (gen-HⁿSⁿ-raw R n) x) r)
snd (HⁿSⁿ-raw≃G-inv R n r) =
  cong (subst (EM (Ring→AbGroup R)) (+'-comm n 0))
        (cong (_⌣ₖ r) (snd (gen-HⁿSⁿ-raw R n))
       ∙ 0ₖ-⌣ₖ n 0 r)
       ∙ λ j → transp (λ i → EM (Ring→AbGroup R)
                               (+'-comm n 0 (i ∨ j)))
                     j (0ₖ (+'-comm n 0 j))


HⁿSⁿ-raw≃G-inv-isInv : (R : Ring ℓ) (n : ℕ) (r : fst R) →
      ((fst (HⁿSⁿ-raw≃G (Ring→AbGroup R) n))
     ∘ HⁿSⁿ-raw≃G-inv R n) r
     ≡ r
HⁿSⁿ-raw≃G-inv-isInv R zero r = transportRefl _ ∙ ·IdL (snd R) r
HⁿSⁿ-raw≃G-inv-isInv R (suc zero) r =
    transportRefl _
  ∙ transportRefl _
  ∙ cong₂ (_+r_ (snd R)) (transportRefl (0r (snd R)))
                         (transportRefl _
                       ∙ ·IdL (snd R) r)
  ∙ +IdL (snd R) r
HⁿSⁿ-raw≃G-inv-isInv R (suc (suc n)) r =
    HⁿSⁿ-raw≃G-ind (Ring→AbGroup R) (suc n) _ ∙
    (cong (fst (HⁿSⁿ-raw≃G (Ring→AbGroup R) (suc n)))
          (→∙Homogeneous≡
            (isHomogeneousEM _)
            (funExt λ z →
              cong (ΩEM+1→EM (suc n)) (lem z)
            ∙ Iso-EM-ΩEM+1 (suc n) .Iso.leftInv (subst (EM (Ring→AbGroup R))
              (+'-comm (suc n) 0) (_⌣ₖ_ {m = 0}
                (fst (gen-HⁿSⁿ-raw R (suc n)) z) r)))))
  ∙ HⁿSⁿ-raw≃G-inv-isInv R (suc n) r
  where
  lem : (z : _)
    → (λ i → subst (EM (Ring→AbGroup R)) (+'-comm (suc (suc n)) 0)
         (fst (gen-HⁿSⁿ-raw R (suc (suc n))) (toSusp (S₊∙ (suc n)) z i) ⌣ₖ r))
         ≡ EM→ΩEM+1 (suc n) (subst (EM (Ring→AbGroup R))
            (+'-comm (suc n) 0)
              (_⌣ₖ_ {m = 0} (fst (gen-HⁿSⁿ-raw R (suc n)) z) r))
  lem z = ((λ j → transp (λ i → typ (Ω (EM∙ (Ring→AbGroup R)
                          (+'-comm (suc (suc n)) 0 (~ j ∨ i))))) (~ j)
            λ i → transp (λ i → EM (Ring→AbGroup R)
                          (+'-comm (suc (suc n)) 0 (~ j ∧ i)))
                          j
                          (fst (gen-HⁿSⁿ-raw R (suc (suc n)))
                           (toSusp (S₊∙ (suc n)) z i) ⌣ₖ r))
         ∙ (λ j → transport (λ i → typ (Ω (EM∙ (Ring→AbGroup R)
                    (isSetℕ (suc (suc n)) (suc (suc n))
                      (+'-comm (suc (suc n)) 0) refl j i))))
                    λ i → _⌣ₖ_ {n = suc (suc n)} {m = zero}
                           (fst (gen-HⁿSⁿ-raw R (suc (suc n)))
                            (toSusp (S₊∙ (suc n)) z i)) r)
         ∙ transportRefl _
         ∙ cong (cong (λ x → _⌣ₖ_ {n = suc (suc n)} {m = zero} x r))
                (cong-∙ (fst (gen-HⁿSⁿ-raw R (suc (suc n))))
                  (merid z) (sym (merid (ptSn (suc n))))
              ∙ cong₂ _∙_ refl
                 (cong sym (cong (EM→ΩEM+1 (suc n))
                           (gen-HⁿSⁿ-raw R (suc n) .snd)
                       ∙ EM→ΩEM+1-0ₖ (suc n)))
              ∙ sym (rUnit _))
         ∙ sym (EM→ΩEM+1-distr⌣ₖ0 n (gen-HⁿSⁿ-raw R (suc n) .fst z) r))
        ∙ cong (EM→ΩEM+1 (suc n))
           (sym (transportRefl _)
          ∙ λ i → subst (EM (Ring→AbGroup R))
                   (isSetℕ (suc n) (suc n) refl (+'-comm (suc n) 0) i)
                   (_⌣ₖ_ {m = 0} (fst (gen-HⁿSⁿ-raw R (suc n)) z) r))

-- Main lemma: HⁿSⁿ-raw≃G-inv (i.e. ⌣ₖ is an equivalence)
isEquiv-HⁿSⁿ-raw≃G-inv : (R : Ring ℓ) (n : ℕ)
  → isEquiv (HⁿSⁿ-raw≃G-inv R n)
isEquiv-HⁿSⁿ-raw≃G-inv R n =
  composesToId→Equiv _ _ (funExt (HⁿSⁿ-raw≃G-inv-isInv R n))
    (HⁿSⁿ-raw≃G (Ring→AbGroup R) n .snd)
