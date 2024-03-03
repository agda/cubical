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

------ Part 1. Functoriality of Hˢᵏᵉˡ ------
Hˢᵏᵉˡ→-pre : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f : finCellMap (suc (suc (suc m))) C D)
  → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→-pre C D m f = finCellMap→HomologyMap m f

private
  Hˢᵏᵉˡ→-pre' : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
    → (f : realise C → realise D)
    → ∥ finCellApprox C D f (suc (suc (suc m))) ∥₁
    → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
  Hˢᵏᵉˡ→-pre' C D m f =
    rec→Set isSetGroupHom
    (λ f → Hˢᵏᵉˡ→-pre C D m (f .fst))
    main
    where
    main : 2-Constant (λ f₁ → Hˢᵏᵉˡ→-pre C D m (f₁ .fst))
    main f g = PT.rec (isSetGroupHom _ _)
      (λ q → finChainHomotopy→HomologyPath _ _
        (cellHom-to-ChainHomotopy _ q) flast)
      (pathToCellularHomotopy _ (fst f) (fst g)
        λ x → funExt⁻ (snd f ∙ sym (snd g)) (fincl flast x))

Hˢᵏᵉˡ→ : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (f : realise C → realise D)
  → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→ {C = C} {D} m f =
  Hˢᵏᵉˡ→-pre' C D m f
    (CWmap→finCellMap C D f (suc (suc (suc m))))

Hˢᵏᵉˡ→β : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  {f : realise C → realise D}
  (ϕ : finCellApprox C D f (suc (suc (suc m))))
  → Hˢᵏᵉˡ→ {C = C} {D} m f ≡ Hˢᵏᵉˡ→-pre C D m (ϕ .fst)
Hˢᵏᵉˡ→β C D m {f = f} ϕ =
  cong (Hˢᵏᵉˡ→-pre' C D m f) (squash₁ _ ∣ ϕ ∣₁)

Hˢᵏᵉˡ→id : (m : ℕ) {C : CWskel ℓ}
  → Hˢᵏᵉˡ→ {C = C} m (idfun _) ≡ idGroupHom
Hˢᵏᵉˡ→id m {C = C} =
  Hˢᵏᵉˡ→β C C m {idfun _} (idFinCellApprox (suc (suc (suc m))))
  ∙ finCellMap→HomologyMapId _

Hˢᵏᵉˡ→comp : (m : ℕ)
  {C : CWskel ℓ} {D : CWskel ℓ'} {E : CWskel ℓ''}
  (g : realise D → realise E)
  (f : realise C → realise D)
  → Hˢᵏᵉˡ→ m (g ∘ f)
  ≡ compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
Hˢᵏᵉˡ→comp m {C = C} {D = D} {E = E} g f =
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

    eq1 : Hˢᵏᵉˡ→ m (g ∘ f)
        ≡ Hˢᵏᵉˡ→-pre C E m (composeFinCellMap _ (fst G) (fst F))
    eq1 = Hˢᵏᵉˡ→β C E m {g ∘ f} comps

    eq2 : compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
        ≡ compGroupHom (Hˢᵏᵉˡ→-pre C D m (fst F)) (Hˢᵏᵉˡ→-pre D E m (fst G))
    eq2 = cong₂ compGroupHom (Hˢᵏᵉˡ→β C D m {f = f} F) (Hˢᵏᵉˡ→β D E m {f = g} G)

    main : Hˢᵏᵉˡ→ m (g ∘ f) ≡ compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
    main = eq1 ∙∙ finCellMap→HomologyMapComp _ _ _ ∙∙ sym eq2

-- preservation of equivalence
Hˢᵏᵉˡ→Iso : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupIso (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Iso.fun (fst (Hˢᵏᵉˡ→Iso m e)) = fst (Hˢᵏᵉˡ→ m (fst e))
Iso.inv (fst (Hˢᵏᵉˡ→Iso m e)) = fst (Hˢᵏᵉˡ→ m (invEq e))
Iso.rightInv (fst (Hˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→comp m (fst e) (invEq e))
       ∙∙ cong (Hˢᵏᵉˡ→ m) (funExt (secEq e))
       ∙∙ Hˢᵏᵉˡ→id m))
Iso.leftInv (fst (Hˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→comp m (invEq e) (fst e))
       ∙∙ cong (Hˢᵏᵉˡ→ m) (funExt (retEq e))
       ∙∙ Hˢᵏᵉˡ→id m))
snd (Hˢᵏᵉˡ→Iso m e) = snd (Hˢᵏᵉˡ→ m (fst e))

Hˢᵏᵉˡ→Equiv : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupEquiv (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→Equiv m e = GroupIso→GroupEquiv (Hˢᵏᵉˡ→Iso m e)


------ Part 2. Definition of cellular homology ------
Hᶜʷ : ∀ (C : CW ℓ) (n : ℕ) → Group₀
Hᶜʷ (C , CWstr) n =
  PropTrunc→Group
      (λ Cskel → Hˢᵏᵉˡ (Cskel .fst) n)
      (λ Cskel Dskel
        → Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))
      coh
      CWstr
  where
  coh : (Cskel Dskel Eskel : isCW C) (t : fst (Hˢᵏᵉˡ (Cskel .fst) n))
    → fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Dskel)) (snd Eskel))))
        (fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))) t)
    ≡ fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Eskel)))) t
  coh (C' , e) (D , f) (E , h) =
    funExt⁻ (cong fst
          (sym (Hˢᵏᵉˡ→comp n (fst (compEquiv (invEquiv f) h))
                           (fst (compEquiv (invEquiv e) f)))
          ∙ cong (Hˢᵏᵉˡ→ n) (funExt λ x → cong (fst h) (retEq f _))))

-- lemmas for functoriality
private
  module _ {C : Type ℓ} {D : Type ℓ'} (f : C → D) (n : ℕ) where
    right : (cwC : isCW C) (cwD1 : isCW D) (cwD2 : isCW D)
      → PathP (λ i → GroupHom (Hᶜʷ (C , ∣ cwC ∣₁) n)
                         (Hᶜʷ (D , squash₁ ∣ cwD1 ∣₁ ∣ cwD2 ∣₁ i) n))
        (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD1) (f (invEq (snd cwC) x))))
        (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD2) (f (invEq (snd cwC) x))))
    right cwC cwD1 cwD2 =
      PathPGroupHomₗ _
        (cong (Hˢᵏᵉˡ→ n) (funExt (λ s
          → cong (fst (snd cwD2)) (sym (retEq (snd cwD1) _))))
        ∙ Hˢᵏᵉˡ→comp n _ _)

    left : (cwC1 : isCW C) (cwC2 : isCW C) (cwD : isCW D)
      → PathP (λ i → GroupHom (Hᶜʷ (C , squash₁ ∣ cwC1 ∣₁ ∣ cwC2 ∣₁ i) n)
                                  (Hᶜʷ (D , ∣ cwD ∣₁) n))
                 (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC1) x))))
                 (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x))))
    left cwC1 cwC2 cwD =
      PathPGroupHomᵣ (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd cwC1)) (snd cwC2)))
            (sym (Hˢᵏᵉˡ→comp n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x)))
                             (compEquiv (invEquiv (snd cwC1)) (snd cwC2) .fst))
           ∙ cong (Hˢᵏᵉˡ→ n) (funExt (λ x
              → cong (fst (snd cwD) ∘ f)
                  (retEq (snd cwC2) _))))

    left-right : (x y : isCW C) (v w : isCW D) →
      SquareP
      (λ i j →
         GroupHom (Hᶜʷ (C , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) n)
         (Hᶜʷ (D , squash₁ ∣ v ∣₁ ∣ w ∣₁ j) n))
      (right x v w) (right y v w) (left x y v) (left x y w)
    left-right _ _ _ _ = isSet→SquareP
       (λ _ _ → isSetGroupHom) _ _ _ _

    Hᶜʷ→pre : (cwC : ∥ isCW C ∥₁) (cwD : ∥ isCW D ∥₁)
      → GroupHom (Hᶜʷ (C , cwC) n) (Hᶜʷ (D , cwD) n)
    Hᶜʷ→pre =
      elim2→Set (λ _ _ → isSetGroupHom)
        (λ cwC cwD → Hˢᵏᵉˡ→ n (fst (snd cwD) ∘ f ∘ invEq (snd cwC)))
        left right
        (λ _ _ _ _ → isSet→SquareP
         (λ _ _ → isSetGroupHom) _ _ _ _)

-- functoriality
Hᶜʷ→ : {C : CW ℓ} {D : CW ℓ'} (n : ℕ) (f : C →ᶜʷ D)
    → GroupHom (Hᶜʷ C n) (Hᶜʷ D n)
Hᶜʷ→ {C = C , cwC} {D = D , cwD} n f = Hᶜʷ→pre f n cwC cwD

Hᶜʷ→id : {C : CW ℓ} (n : ℕ)
    → Hᶜʷ→ {C = C} {C} n (idfun (fst C))
     ≡ idGroupHom
Hᶜʷ→id {C = C , cwC} n =
  PT.elim {P = λ cwC
    → Hᶜʷ→ {C = C , cwC} {C , cwC} n (idfun C) ≡ idGroupHom}
    (λ _ → isSetGroupHom _ _)
    (λ cwC* → cong (Hˢᵏᵉˡ→ n) (funExt (secEq (snd cwC*)))
              ∙ Hˢᵏᵉˡ→id n) cwC

Hᶜʷ→comp : {C : CW ℓ} {D : CW ℓ'} {E : CW ℓ''} (n : ℕ)
      (g : D →ᶜʷ E) (f : C →ᶜʷ D)
    → Hᶜʷ→ {C = C} {E} n (g ∘ f)
     ≡ compGroupHom (Hᶜʷ→ {C = C} {D} n f) (Hᶜʷ→ {C = D} {E} n g)
Hᶜʷ→comp {C = C , cwC} {D = D , cwD} {E = E , cwE} n g f =
  PT.elim3 {P = λ cwC cwD cwE
    → Hᶜʷ→ {C = C , cwC} {E , cwE} n (g ∘ f)
     ≡ compGroupHom (Hᶜʷ→ {C = C , cwC} {D , cwD} n f)
                    (Hᶜʷ→ {C = D , cwD} {E , cwE} n g)}
     (λ _ _ _ → isSetGroupHom _ _)
     (λ cwC cwD cwE
       → cong (Hˢᵏᵉˡ→ n) (funExt (λ x → cong (fst (snd cwE) ∘ g)
                          (sym (retEq (snd cwD) _))))
       ∙ Hˢᵏᵉˡ→comp n _ _)
     cwC cwD cwE

-- preservation of equivalence
Hᶜʷ→Iso : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupIso (Hᶜʷ C m) (Hᶜʷ D m)
Iso.fun (fst (Hᶜʷ→Iso m e)) = fst (Hᶜʷ→ m (fst e))
Iso.inv (fst (Hᶜʷ→Iso m e)) = fst (Hᶜʷ→ m (invEq e))
Iso.rightInv (fst (Hᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hᶜʷ→comp m (fst e) (invEq e))
       ∙∙ cong (Hᶜʷ→ m) (funExt (secEq e))
       ∙∙ Hᶜʷ→id m))
Iso.leftInv (fst (Hᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hᶜʷ→comp m (invEq e) (fst e))
       ∙∙ cong (Hᶜʷ→ m) (funExt (retEq e))
       ∙∙ Hᶜʷ→id m))
snd (Hᶜʷ→Iso m e) = snd (Hᶜʷ→ m (fst e))

Hᶜʷ→Equiv : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupEquiv (Hᶜʷ C m) (Hᶜʷ D m)
Hᶜʷ→Equiv m e = GroupIso→GroupEquiv (Hᶜʷ→Iso m e)
