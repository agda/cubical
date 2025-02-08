{-# OPTIONS --safe --lossy-unification #-}
{-
This file contains:
1. Functoriality of Hˢᵏᵉˡ
2. Construction of cellular homology, including funtoriality
-}

module Cubical.CW.Homology where

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map
open import Cubical.CW.Homotopy
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.ChainComplex

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SequentialColimit

private
  variable
    ℓ ℓ' ℓ'' : Level

------ Part 1. Functoriality of H̃ˢᵏᵉˡ ------
H̃ˢᵏᵉˡ→-pre : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f : finCellMap (suc (suc (suc m))) C D)
  → GroupHom (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
H̃ˢᵏᵉˡ→-pre C D m f = finCellMap→HomologyMap m f

private
  H̃ˢᵏᵉˡ→-pre' : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
    → (f : realise C → realise D)
    → ∥ finCellApprox C D f (suc (suc (suc m))) ∥₁
    → GroupHom (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
  H̃ˢᵏᵉˡ→-pre' C D m f =
    rec→Set isSetGroupHom
    (λ f → H̃ˢᵏᵉˡ→-pre C D m (f .fst))
    main
    where
    main : 2-Constant (λ f₁ → H̃ˢᵏᵉˡ→-pre C D m (f₁ .fst))
    main f g = PT.rec (isSetGroupHom _ _)
      (λ q → finChainHomotopy→HomologyPath _ _
        (cellHom-to-ChainHomotopy _ q) flast)
      (pathToCellularHomotopy _ (fst f) (fst g)
        λ x → funExt⁻ (snd f ∙ sym (snd g)) (fincl flast x))

H̃ˢᵏᵉˡ→ : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (f : realise C → realise D)
  → GroupHom (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
H̃ˢᵏᵉˡ→ {C = C} {D} m f =
  H̃ˢᵏᵉˡ→-pre' C D m f
    (CWmap→finCellMap C D f (suc (suc (suc m))))

H̃ˢᵏᵉˡ→β : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  {f : realise C → realise D}
  (ϕ : finCellApprox C D f (suc (suc (suc m))))
  → H̃ˢᵏᵉˡ→ {C = C} {D} m f ≡ H̃ˢᵏᵉˡ→-pre C D m (ϕ .fst)
H̃ˢᵏᵉˡ→β C D m {f = f} ϕ =
  cong (H̃ˢᵏᵉˡ→-pre' C D m f) (squash₁ _ ∣ ϕ ∣₁)

H̃ˢᵏᵉˡ→id : (m : ℕ) {C : CWskel ℓ}
  → H̃ˢᵏᵉˡ→ {C = C} m (idfun _) ≡ idGroupHom
H̃ˢᵏᵉˡ→id m {C = C} =
  H̃ˢᵏᵉˡ→β C C m {idfun _} (idFinCellApprox (suc (suc (suc m))))
  ∙ finCellMap→HomologyMapId _

H̃ˢᵏᵉˡ→comp : (m : ℕ)
  {C : CWskel ℓ} {D : CWskel ℓ'} {E : CWskel ℓ''}
  (g : realise D → realise E)
  (f : realise C → realise D)
  → H̃ˢᵏᵉˡ→ m (g ∘ f)
  ≡ compGroupHom (H̃ˢᵏᵉˡ→ m f) (H̃ˢᵏᵉˡ→ m g)
H̃ˢᵏᵉˡ→comp m {C = C} {D = D} {E = E} g f =
  PT.rec2 (isSetGroupHom _ _)
    main
    (CWmap→finCellMap C D f (suc (suc (suc m))))
    (CWmap→finCellMap D E g (suc (suc (suc m))))
  where
  module _  (F : finCellApprox C D f (suc (suc (suc m))))
            (G : finCellApprox D E g (suc (suc (suc m))))
    where
    comps : finCellApprox C E (g ∘ f) (suc (suc (suc m)))
    comps = compFinCellApprox _ {g = g} {f} G F

    eq1 : H̃ˢᵏᵉˡ→ m (g ∘ f)
        ≡ H̃ˢᵏᵉˡ→-pre C E m (composeFinCellMap _ (fst G) (fst F))
    eq1 = H̃ˢᵏᵉˡ→β C E m {g ∘ f} comps

    eq2 : compGroupHom (H̃ˢᵏᵉˡ→ m f) (H̃ˢᵏᵉˡ→ m g)
        ≡ compGroupHom (H̃ˢᵏᵉˡ→-pre C D m (fst F)) (H̃ˢᵏᵉˡ→-pre D E m (fst G))
    eq2 = cong₂ compGroupHom (H̃ˢᵏᵉˡ→β C D m {f = f} F) (H̃ˢᵏᵉˡ→β D E m {f = g} G)

    main : H̃ˢᵏᵉˡ→ m (g ∘ f) ≡ compGroupHom (H̃ˢᵏᵉˡ→ m f) (H̃ˢᵏᵉˡ→ m g)
    main = eq1 ∙∙ finCellMap→HomologyMapComp _ _ _ ∙∙ sym eq2

-- preservation of equivalence
H̃ˢᵏᵉˡ→Iso : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupIso (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
Iso.fun (fst (H̃ˢᵏᵉˡ→Iso m e)) = fst (H̃ˢᵏᵉˡ→ m (fst e))
Iso.inv (fst (H̃ˢᵏᵉˡ→Iso m e)) = fst (H̃ˢᵏᵉˡ→ m (invEq e))
Iso.rightInv (fst (H̃ˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→comp m (fst e) (invEq e))
       ∙∙ cong (H̃ˢᵏᵉˡ→ m) (funExt (secEq e))
       ∙∙ H̃ˢᵏᵉˡ→id m))
Iso.leftInv (fst (H̃ˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→comp m (invEq e) (fst e))
       ∙∙ cong (H̃ˢᵏᵉˡ→ m) (funExt (retEq e))
       ∙∙ H̃ˢᵏᵉˡ→id m))
snd (H̃ˢᵏᵉˡ→Iso m e) = snd (H̃ˢᵏᵉˡ→ m (fst e))

H̃ˢᵏᵉˡ→Equiv : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupEquiv (H̃ˢᵏᵉˡ C m) (H̃ˢᵏᵉˡ D m)
H̃ˢᵏᵉˡ→Equiv m e = GroupIso→GroupEquiv (H̃ˢᵏᵉˡ→Iso m e)


------ Part 2. Definition of cellular homology ------
H̃ᶜʷ : ∀ (C : CW ℓ) (n : ℕ) → Group₀
H̃ᶜʷ (C , CWstr) n =
  PropTrunc→Group
      (λ Cskel → H̃ˢᵏᵉˡ (Cskel .fst) n)
      (λ Cskel Dskel
        → H̃ˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))
      coh
      CWstr
  where
  coh : (Cskel Dskel Eskel : isCW C) (t : fst (H̃ˢᵏᵉˡ (Cskel .fst) n))
    → fst (fst (H̃ˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Dskel)) (snd Eskel))))
        (fst (fst (H̃ˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))) t)
    ≡ fst (fst (H̃ˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Eskel)))) t
  coh (C' , e) (D , f) (E , h) =
    funExt⁻ (cong fst
          (sym (H̃ˢᵏᵉˡ→comp n (fst (compEquiv (invEquiv f) h))
                           (fst (compEquiv (invEquiv e) f)))
          ∙ cong (H̃ˢᵏᵉˡ→ n) (funExt λ x → cong (fst h) (retEq f _))))

-- lemmas for functoriality
private
  module _ {C : Type ℓ} {D : Type ℓ'} (f : C → D) (n : ℕ) where
    right : (cwC : isCW C) (cwD1 : isCW D) (cwD2 : isCW D)
      → PathP (λ i → GroupHom (H̃ᶜʷ (C , ∣ cwC ∣₁) n)
                         (H̃ᶜʷ (D , squash₁ ∣ cwD1 ∣₁ ∣ cwD2 ∣₁ i) n))
        (H̃ˢᵏᵉˡ→ n (λ x → fst (snd cwD1) (f (invEq (snd cwC) x))))
        (H̃ˢᵏᵉˡ→ n (λ x → fst (snd cwD2) (f (invEq (snd cwC) x))))
    right cwC cwD1 cwD2 =
      PathPGroupHomₗ _
        (cong (H̃ˢᵏᵉˡ→ n) (funExt (λ s
          → cong (fst (snd cwD2)) (sym (retEq (snd cwD1) _))))
        ∙ H̃ˢᵏᵉˡ→comp n _ _)

    left : (cwC1 : isCW C) (cwC2 : isCW C) (cwD : isCW D)
      → PathP (λ i → GroupHom (H̃ᶜʷ (C , squash₁ ∣ cwC1 ∣₁ ∣ cwC2 ∣₁ i) n)
                                  (H̃ᶜʷ (D , ∣ cwD ∣₁) n))
                 (H̃ˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC1) x))))
                 (H̃ˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x))))
    left cwC1 cwC2 cwD =
      PathPGroupHomᵣ (H̃ˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd cwC1)) (snd cwC2)))
            (sym (H̃ˢᵏᵉˡ→comp n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x)))
                             (compEquiv (invEquiv (snd cwC1)) (snd cwC2) .fst))
           ∙ cong (H̃ˢᵏᵉˡ→ n) (funExt (λ x
              → cong (fst (snd cwD) ∘ f)
                  (retEq (snd cwC2) _))))

    left-right : (x y : isCW C) (v w : isCW D) →
      SquareP
      (λ i j →
         GroupHom (H̃ᶜʷ (C , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) n)
         (H̃ᶜʷ (D , squash₁ ∣ v ∣₁ ∣ w ∣₁ j) n))
      (right x v w) (right y v w) (left x y v) (left x y w)
    left-right _ _ _ _ = isSet→SquareP
       (λ _ _ → isSetGroupHom) _ _ _ _

    H̃ᶜʷ→pre : (cwC : ∥ isCW C ∥₁) (cwD : ∥ isCW D ∥₁)
      → GroupHom (H̃ᶜʷ (C , cwC) n) (H̃ᶜʷ (D , cwD) n)
    H̃ᶜʷ→pre =
      elim2→Set (λ _ _ → isSetGroupHom)
        (λ cwC cwD → H̃ˢᵏᵉˡ→ n (fst (snd cwD) ∘ f ∘ invEq (snd cwC)))
        left right
        (λ _ _ _ _ → isSet→SquareP
         (λ _ _ → isSetGroupHom) _ _ _ _)

-- functoriality
H̃ᶜʷ→ : {C : CW ℓ} {D : CW ℓ'} (n : ℕ) (f : C →ᶜʷ D)
    → GroupHom (H̃ᶜʷ C n) (H̃ᶜʷ D n)
H̃ᶜʷ→ {C = C , cwC} {D = D , cwD} n f = H̃ᶜʷ→pre f n cwC cwD

H̃ᶜʷ→id : {C : CW ℓ} (n : ℕ)
    → H̃ᶜʷ→ {C = C} {C} n (idfun (fst C))
     ≡ idGroupHom
H̃ᶜʷ→id {C = C , cwC} n =
  PT.elim {P = λ cwC
    → H̃ᶜʷ→ {C = C , cwC} {C , cwC} n (idfun C) ≡ idGroupHom}
    (λ _ → isSetGroupHom _ _)
    (λ cwC* → cong (H̃ˢᵏᵉˡ→ n) (funExt (secEq (snd cwC*)))
              ∙ H̃ˢᵏᵉˡ→id n) cwC

H̃ᶜʷ→comp : {C : CW ℓ} {D : CW ℓ'} {E : CW ℓ''} (n : ℕ)
      (g : D →ᶜʷ E) (f : C →ᶜʷ D)
    → H̃ᶜʷ→ {C = C} {E} n (g ∘ f)
     ≡ compGroupHom (H̃ᶜʷ→ {C = C} {D} n f) (H̃ᶜʷ→ {C = D} {E} n g)
H̃ᶜʷ→comp {C = C , cwC} {D = D , cwD} {E = E , cwE} n g f =
  PT.elim3 {P = λ cwC cwD cwE
    → H̃ᶜʷ→ {C = C , cwC} {E , cwE} n (g ∘ f)
     ≡ compGroupHom (H̃ᶜʷ→ {C = C , cwC} {D , cwD} n f)
                    (H̃ᶜʷ→ {C = D , cwD} {E , cwE} n g)}
     (λ _ _ _ → isSetGroupHom _ _)
     (λ cwC cwD cwE
       → cong (H̃ˢᵏᵉˡ→ n) (funExt (λ x → cong (fst (snd cwE) ∘ g)
                          (sym (retEq (snd cwD) _))))
       ∙ H̃ˢᵏᵉˡ→comp n _ _)
     cwC cwD cwE

-- preservation of equivalence
H̃ᶜʷ→Iso : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupIso (H̃ᶜʷ C m) (H̃ᶜʷ D m)
Iso.fun (fst (H̃ᶜʷ→Iso m e)) = fst (H̃ᶜʷ→ m (fst e))
Iso.inv (fst (H̃ᶜʷ→Iso m e)) = fst (H̃ᶜʷ→ m (invEq e))
Iso.rightInv (fst (H̃ᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (H̃ᶜʷ→comp m (fst e) (invEq e))
       ∙∙ cong (H̃ᶜʷ→ m) (funExt (secEq e))
       ∙∙ H̃ᶜʷ→id m))
Iso.leftInv (fst (H̃ᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (H̃ᶜʷ→comp m (invEq e) (fst e))
       ∙∙ cong (H̃ᶜʷ→ m) (funExt (retEq e))
       ∙∙ H̃ᶜʷ→id m))
snd (H̃ᶜʷ→Iso m e) = snd (H̃ᶜʷ→ m (fst e))

H̃ᶜʷ→Equiv : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupEquiv (H̃ᶜʷ C m) (H̃ᶜʷ D m)
H̃ᶜʷ→Equiv m e = GroupIso→GroupEquiv (H̃ᶜʷ→Iso m e)
