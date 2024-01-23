{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Torus where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv



open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Instances.DirectProduct


open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 renaming (rec to S¹fun ; elim to S¹elim)


open import Cubical.Data.Unit

-- Preliminary lemmas
elimFunT² : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ)
  (p q : typ (Ω (EM∙ G (suc n))))
   → Square q q p p
   → S¹ × S¹ → EM G (suc n)
elimFunT² n p q P (base , base) = 0ₖ (suc n)
elimFunT² n p q P (base , loop i) = q i
elimFunT² n p q P (loop i , base) = p i
elimFunT² n p q P (loop i , loop j) = P i j

elimFunT²' : ∀ {ℓ} {G : AbGroup ℓ}
  (n : ℕ) → Square (refl {ℓ} {EM G (suc n)} {0ₖ (suc n)}) refl refl refl
           → S¹ × S¹ → EM G (suc n)
elimFunT²' n P (x , base) = 0ₖ (suc n)
elimFunT²' n P (base , loop j) = 0ₖ (suc n)
elimFunT²' n P (loop i , loop j) = P i j

elimFunT²'≡elimFunT² : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ)
  → (P : _) → elimFunT²' {G = G} n P ≡ elimFunT² n refl refl P
elimFunT²'≡elimFunT² n P i (base , base) = 0ₖ (suc n)
elimFunT²'≡elimFunT² n P i (base , loop k) = 0ₖ (suc n)
elimFunT²'≡elimFunT² n P i (loop j , base) = 0ₖ (suc n)
elimFunT²'≡elimFunT² n P i (loop j , loop k) = P j k

coHomPointedElimT² : ∀ {ℓ ℓ'} {G : AbGroup ℓ} (n : ℕ) {B : coHom (suc n) G (S¹ × S¹) → Type ℓ'}
                 → ((x : coHom (suc n) G (S¹ × S¹)) → isProp (B x))
                 → ((p q : _) (P : _) → B ∣ elimFunT² n p q P ∣₂)
                 → (x : coHom (suc n) G (S¹ × S¹)) → B x
coHomPointedElimT² {G = G} n {B = B} isprop indp =
  coHomPointedElim n (base , base) isprop
    λ f fId → subst B (cong ∣_∣₂ (funExt
      (λ { (base , base) → sym fId
         ; (base , loop i) j → helper f fId i1 i (~ j)
         ; (loop i , base) j → helper f fId i i1 (~ j)
         ; (loop i , loop j) k → helper f fId i j (~ k)})))
        (indp (λ i → helper f fId i i1 i1)
              (λ i → helper f fId i1 i i1)
               λ i j → helper f fId i j i1)
    where
    helper : (f : S¹ × S¹ → EM G (suc n)) → f (base , base) ≡ 0ₖ (suc n)
           → I → I → I → EM G (suc n)
    helper f fId i j k =
      hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (i = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (j = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i
                     ; (j = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i})
            (inS (f ((loop i) , (loop j))))
            k

private
  lem : ∀ {ℓ ℓ'} {G : AbGroup ℓ} (n : ℕ) {B : coHom (2 + n) G (S¹ × S¹) → Type ℓ'}
                   → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                   → (p : _) → (refl ≡ p)
                   → (q : _) → (refl ≡ q)
                   → (P : _)
                   → B ∣ elimFunT² (suc n) p q P ∣₂
  lem n {B = B} elimP p =
    J (λ p _ → (q : _) → (refl ≡ q)
             → (P : _)
             → B ∣ elimFunT² (suc n) p q P ∣₂)
      λ q →
        J (λ q _ → (P : _) → B ∣ elimFunT² (suc n) refl q P ∣₂)
           elimP

{- When working with Hⁿ(T²) , n ≥ 2, we are, in the case described above, allowed to assume that any f : Hⁿ(T²) is
   elimFunT² n refl refl P -}
coHomPointedElimT²' : ∀ {ℓ ℓ'} {G : AbGroup ℓ} (n : ℕ) {B : coHom (2 + n) G (S¹ × S¹) → Type ℓ'}
                 → ((x : coHom (2 + n) G (S¹ × S¹)) → isProp (B x))
                 → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                 → (x : coHom (2 + n) G (S¹ × S¹)) → B x
coHomPointedElimT²' n {B = B} prop ind =
  coHomPointedElimT² (suc n) prop
    λ p q P → Trunc.rec (isProp→isOfHLevelSuc n (prop _))
      (λ p-refl → Trunc.rec (isProp→isOfHLevelSuc n (prop _))
                         (λ q-refl → lem n {B = B} ind p (sym p-refl) q (sym q-refl) P)
      (isConnectedPath (suc n)
        (isConnectedPath (suc (suc n)) (isConnectedEM (suc (suc n))) _ _) q refl .fst))
      (isConnectedPath (suc n)
        (isConnectedPath (suc (suc n)) (isConnectedEM (suc (suc n))) _ _) p refl .fst)

{- A slight variation of the above which gives definitional equalities for all points (x , base) -}
private
  coHomPointedElimT²'' :  ∀ {ℓ ℓ'} {G : AbGroup ℓ} (n : ℕ) {B : coHom (2 + n) G (S¹ × S¹) → Type ℓ'}
                   → ((x : coHom (2 + n) G (S¹ × S¹)) → isProp (B x))
                   → ((P : _) → B ∣ elimFunT²' (suc n) P ∣₂)
                   → (x : coHom (2 + n) G (S¹ × S¹)) → B x
  coHomPointedElimT²'' n {B = B} prop ind =
    coHomPointedElimT²' n prop λ P → subst (λ x → B ∣ x ∣₂)
                        (elimFunT²'≡elimFunT² (suc n) P) (ind P)

--------- H⁰(T²) ------------
H⁰[T²,G]≅G : ∀ {ℓ} (G : AbGroup ℓ) → AbGroupEquiv (coHomGr 0 G (S₊ 1 × S₊ 1)) G
H⁰[T²,G]≅G = H⁰conn (∣ base , base ∣
                  , Trunc.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                    λ ab → PT.rec2 (isOfHLevelTrunc 2 _ _)
                      (λ p q i → ∣ p i , q i ∣ₕ )
                      (isConnectedS¹ (fst ab))
                      (isConnectedS¹ (snd ab)))

--------- H¹(T²) -------------------------------

H¹[T²,G]≅G×G : ∀ {ℓ} (G : AbGroup ℓ)
  → AbGroupEquiv (coHomGr 1 G (S¹ × S¹)) (AbDirProd G G)
H¹[T²,G]≅G×G G =
    (compGroupEquiv
      (invGroupEquiv (GroupIso→GroupEquiv theIso))
    (GroupEquivDirProd
      (H¹[S¹,G]≅G G)
      (H¹[S¹,G]≅G G)))
  where
  _+1_ :  EM G 1 →  EM G 1 →  EM G 1
  _+1_ = _+ₖ_ {G = G} {n = 1}

  typIso : Iso _ _
  Iso.fun typIso = ST.rec (isSet× squash₂ squash₂)
    λ f → ∣ (λ x → f (x , base)) ∣₂ ,  ∣ (λ x → f (base , x)) ∣₂
  Iso.inv typIso = uncurry (ST.rec2 squash₂
    λ f g → ∣ (λ x → f (fst x) +1 g (snd x)) ∣₂)
  Iso.rightInv typIso =
    uncurry (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× squash₂ squash₂) _ _)
      (S¹-connElim (isConnectedEM {G' = G} 1)
                   (λ _ → isPropΠ λ _ → isSet× squash₂ squash₂ _ _)
        (0ₖ  {G = G} 1)
        λ p → S¹-connElim (isConnectedEM {G' = G} 1)
                (λ _ → isSet× squash₂ squash₂ _ _)
                (0ₖ {G = G} 1)
                λ q i → ∣ (λ l → rUnitₖ {G = G} 1 (S¹fun (0ₖ {G = G} 1) p l) i) ∣₂
                        , ∣ S¹fun (0ₖ {G = G} 1) q ∣₂))
  Iso.leftInv typIso = coHomPointedElimT² {G = G} 0 (λ _ → squash₂ _ _)
    λ p q r → cong ∣_∣₂
      (funExt (uncurry (S¹elim _ (λ _ → refl)
        (funExt (toPropElim (λ _ → isOfHLevelPathP' 1 (hLevelEM G 1 _ _) _ _ )
          λ i j → rUnitₖ {G = G} 1 (p i) j)))))

  theIso : AbGroupIso (AbDirProd (coHomGr 1 G S¹) (coHomGr 1 G S¹))  (coHomGr 1 G (S¹ × S¹))
  fst theIso = invIso typIso
  snd theIso = makeIsGroupHom
    (uncurry (ST.elim2 (λ _ _ → isSetΠ λ _ → isSetPathImplicit)
      λ f1 g1 → uncurry (ST.elim2 (λ _ _ → isSetPathImplicit)
        λ f2 g2 → cong ∣_∣₂ (funExt λ {(x , y)
          → move4 (f1 x) (f2 x) (g1 y) (g2 y) _+1_ (assocₖ {G = G} 1) (commₖ {G = G} 1)}))))

----------------------- H²(T²) ------------------------------

H²[T²,G]≅G : ∀ {ℓ} (G : AbGroup ℓ) → AbGroupEquiv (coHomGr 2 G (S¹ × S¹)) G
H²[T²,G]≅G G = compGroupEquiv (GroupIso→GroupEquiv theIso) (Hⁿ[Sⁿ,G]≅G G 0)
  where
  _+1_ :  EM G 1 →  EM G 1 →  EM G 1
  _+1_ = _+ₖ_ {G = G} {n = 1}

  _+2_ :  EM G 2 →  EM G 2 →  EM G 2
  _+2_ = _+ₖ_ {G = G} {n = 2}


  is1 : Iso (S¹ → EM G 2) (EM G 2 × EM G 1)
  is1 = compIso IsoFunSpaceS¹
         (Σ-cong-iso-snd λ t → invIso (Iso-EM-ΩEM+1-gen {G = G} 1 t))

  is : Iso _ _
  is = compIso (setTruncIso (compIso curryIso
        (compIso (codomainIso is1) toProdIso)))
         (compIso setTruncOfProdIso
           (compIso (prodIso
             (equivToIso (fst (Hᵐ⁺ⁿ[Sⁿ,G]≅0 G 0 0))) idIso)
             lUnit*×Iso))

  theIso : AbGroupIso  (coHomGr 2 G (S¹ × S¹)) (coHomGr 1 G S¹)
  fst theIso = is
  snd theIso = makeIsGroupHom
    (coHomPointedElimT²'' {G = G} 0 (λ _ → isPropΠ λ _ → squash₂ _ _)
    λ p → coHomPointedElimT²'' {G = G} 0 (λ _ → squash₂ _ _)
     λ q → cong ∣_∣₂ (funExt λ x
      → cong (ΩEM+1→EM {G = G} 1) (help p q x)
       ∙ ΩEM+1→EM-hom {G = G} 1 (λ i → elimFunT²' {G = G} 1 p (x , loop i))
                                 (λ i → elimFunT²' {G = G} 1 q (x , loop i))))
    where
    help : (p q : Path (0ₖ {G = G} 2 ≡ 0ₖ {G = G} 2) refl refl) (x : S¹)
      → (λ i → elimFunT²' 1 p (x , loop i) +2 elimFunT²' 1 q (x , loop i))
      ≡ (λ i → elimFunT²' 1 p (x , loop i)) ∙ (λ i → elimFunT²' 1 q (x , loop i))
    help p q x = cong₂+₂ {G = G} 0 (cong (λ y → elimFunT²' {G = G} 1 p (x , y)) loop)
                                  (cong (λ y → elimFunT²' {G = G} 1 q (x , y)) loop)

H³⁺ⁿ[T²,G]≅0 : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ)
  → AbGroupEquiv (coHomGr (3 + n) G (S¹ × S¹)) (trivialAbGroup {ℓ})
fst (H³⁺ⁿ[T²,G]≅0 G n) =
  isoToEquiv (isContr→Iso
           (0ₕ (3 + n)
           , coHomPointedElimT²'' {G = G} (suc n)
               (λ _ → squash₂ _ _)
                 λ P → Trunc.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
                     (λ P → cong ∣_∣₂ (funExt λ { (base , base) → refl
                                               ; (base , loop i) → refl
                                               ; (loop i , base) → refl
                                               ; (loop i , loop j) k → P k i j}))
      (isConnectedPath (suc n) (isConnectedPath (2 + n)
        (isConnectedPath (3 + n) (isConnectedEM (3 + n)) _ _) _ _) refl P .fst))
             isContrUnit*)
snd (H³⁺ⁿ[T²,G]≅0 G n) = makeIsGroupHom λ _ _ → refl
