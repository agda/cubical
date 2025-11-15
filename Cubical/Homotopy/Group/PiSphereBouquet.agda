{-# OPTIONS --lossy-unification #-}
{-
This file computes πₙ(⋁ₐSⁿ) for wedge sums over finite sets and n ≥ 2.
-}
module Cubical.Homotopy.Group.PiSphereBouquet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB
open import Cubical.Algebra.Group.Instances.Pi

open import Cubical.Axiom.Choice

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Wedge
open import Cubical.HITs.SphereBouquet.Degree

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Group.PinSn

open import Cubical.ZCohomology.Groups.Sn

-- ⋁Sⁿ → ΠSⁿ
⋁Sphere→ΠSphere : {n k : ℕ} → SphereBouquet n (Fin k) → (Fin k → S₊ n)
⋁Sphere→ΠSphere a b = pickPetal b a

isConnected⋁Sphere→ΠSphere : {n k : ℕ}
  → isConnectedFun (suc n + suc n) (⋁Sphere→ΠSphere {n = suc n} {suc k})
isConnected⋁Sphere→ΠSphere {n = n} {k = zero} =
  subst (isConnectedFun (suc n + suc n))
    (funExt (λ x → funExt (lem x)))
    (isEquiv→isConnected _ (isoToIsEquiv main) _)
  where
  cntr = isContr→≃Unit (inhProp→isContr fzero isPropFin1)

  main : Iso (SphereBouquet (suc n) (Fin 1)) (Fin 1 → S₊ (suc n))
  main = compIso (compIso (compIso
     ((PushoutAlongEquiv cntr _))
      (compIso (Σ-cong-iso (equivToIso cntr) λ _ → idIso) lUnit×Iso))
      (invIso (ΠUnitIso ( λ _ → S₊ (suc n)))))
    (domIso (equivToIso (invEquiv cntr)))

  lem :  (x : _) (y : _) → Iso.fun main x y ≡ ⋁Sphere→ΠSphere x y
  lem (inl x) y = refl
  lem (inr ((zero , tt) , x)) (zero , tt) = refl
  lem (push (zero , tt) i) (zero , tt) = refl
isConnected⋁Sphere→ΠSphere {n = n} {k = suc k} =
  subst (isConnectedFun (suc n + suc n))
    (λ i x y → g≡ (isConnected⋁Sphere→ΠSphere {k = k}) x y i)
    (isConnectedg (isConnected⋁Sphere→ΠSphere {k = k}))
  where
  conLem : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''}
     (f : A → A') {n}
    → isConnectedFun n f → isConnectedFun n (map-× f (idfun B))
  conLem f cf (a , b) = isConnectedRetractFromIso _
    (compIso (Σ-cong-iso-snd (λ _ → invIso ΣPathIsoPathΣ))
      (compIso Σ-assoc-Iso
         (Σ-cong-iso-snd
          (λ x → compIso (invIso Σ-assoc-Iso)
            (compIso (Σ-cong-iso-fst Σ-swap-Iso)
              (compIso Σ-assoc-Iso
                (compIso (Σ-cong-iso-snd
                  (λ s →
                    compIso (Σ-cong-iso-snd
                      λ b → iso sym sym (λ _ → refl) (λ _ → refl))
                      (equivToIso (isContr→≃Unit
                      (isContrSingl _)))))
                  rUnit×Iso))))))) (cf a)

  module _ (ind : isConnectedFun (suc n + suc n)
                   (⋁Sphere→ΠSphere {n = suc n} {suc k})) where
    g : SphereBouquet (suc n) (Fin (suc (suc k)))
        → Fin (suc (suc k)) → S₊ (suc n)
    g = Iso.inv (Iso-FinSuc→-Fin→× (suc k))
      ∘ map-× (⋁Sphere→ΠSphere {n = suc n} {suc k}) (idfun _)
      ∘ ⋁↪
      ∘ Iso.fun Iso-⋁genFinSuc-⋁genFin⋁

    g≡inl : (y : _) → g (inl tt) y ≡ ⋁Sphere→ΠSphere (inl tt) y
    g≡inl (zero , y) = refl
    g≡inl (suc s , y) = refl

    g≡inr : (x : _) (y : _) → g (inr x) y ≡ ⋁Sphere→ΠSphere (inr x) y
    g≡inr ((zero , t) , q) (zero , p) = refl
    g≡inr ((zero , t) , q) (suc x , p) = refl
    g≡inr ((suc s , t) , q) (zero , p) = refl
    g≡inr ((suc s , t) , q) (suc x , p) with (x ≟ᵗ s)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    g≡inlr : (x : _) (y : _)
      → Square (λ i → g (push x i) y) (λ i → ⋁Sphere→ΠSphere (push x i) y)
               (g≡inl y) (g≡inr (x , ptSn (suc n)) y)
    g≡inlr (zero , t) (zero , p) = refl
    g≡inlr (suc s , t) (zero , p) = refl
    g≡inlr (zero , t) (suc x , p) = refl
    g≡inlr (suc s , t) (suc x , p) with (x ≟ᵗ s)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    g≡ : (x : _) (y : _) → g x y ≡ ⋁Sphere→ΠSphere x y
    g≡ (inl x) = g≡inl
    g≡ (inr x) = g≡inr x
    g≡ (push x i) y j = g≡inlr x y j i

    isConnectedg : isConnectedFun (suc n + suc n) g
    isConnectedg =
      isConnectedComp (Iso.inv (Iso-FinSuc→-Fin→× (suc k))) _ _
        (isEquiv→isConnected _
          (isoToIsEquiv (invIso (Iso-FinSuc→-Fin→× (suc k)))) (suc n + suc n))
        (isConnectedComp
          (map-× (⋁Sphere→ΠSphere {n = suc n} {suc k}) (idfun _))
          _ (suc n + suc n)
          (conLem _ ind)
          (isConnectedComp ⋁↪ _ _
            (isConnected⋁↪
                isConnectedSphereBouquet' (sphereConnected (suc n)))
            (isEquiv→isConnected _ (isoToIsEquiv Iso-⋁genFinSuc-⋁genFin⋁)
             (suc n + suc n))))

-- πₙ(ΠₐSⁿ) ≅ℤ[a]
πₙΠSⁿ≅ℤ[] : (n k : ℕ)
  → GroupIso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
              (AbGroup→Group ℤ[Fin k ])
πₙΠSⁿ≅ℤ[] n k = compGroupIso is3 is4
  where
  is1 : (n : ℕ)
    → Iso (S₊∙ (suc n) →∙ ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
           (Fin k → S₊∙ (suc n) →∙ S₊∙ (suc n))
  fst (Iso.fun (is1 n) (f , s) x) y = f y x
  snd (Iso.fun (is1 n) (f , s) x) = funExt⁻ s x
  fst (Iso.inv (is1 n) f) y x = f x .fst y
  snd (Iso.inv (is1 n) f) i x = f x .snd i
  Iso.rightInv (is1 n) f = refl
  Iso.leftInv (is1 n) f = refl

  is2 : (n : ℕ)
    → Iso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))) .fst)
           (Fin k → π'Gr n (S₊∙ (suc n)) .fst)
  is2 n = compIso (setTruncIso (is1 n))
         (compIso
           setTruncTrunc2Iso
           (compIso (equivToIso (_ , InductiveFinSatAC 2 k _))
             (codomainIso (invIso setTruncTrunc2Iso))))

  is3 : GroupIso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
                (ΠGroup (λ (x : Fin k) → π'Gr n (S₊∙ (suc n))))
  fst is3 = is2 n
  snd is3 = makeIsGroupHom (ST.elim2
    (λ _ _ → isOfHLevelPath 2 (isSetΠ (λ _ → squash₂)) _ _)
    λ f g → funExt λ x → cong ∣_∣₂ (lem n f g x))
    where
    lem : (n : ℕ)
      → (f g : S₊∙ (suc n) →∙ ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
      → (x : _) → Iso.fun (is1 n) (∙Π f g) x
                 ≡ ∙Π (Iso.fun (is1 n) f x) (Iso.fun (is1 n) g x)
    lem zero f g x =
      ΣPathP ((funExt (λ { base → refl ; (loop i) → refl})) , refl)
    lem (suc n) f g x =
      ΣPathP ((funExt (λ { north → refl ; south → refl ; (merid a i) → refl}))
             , refl)

  is4 : GroupIso (ΠGroup (λ (x : Fin k) → π'Gr n (S₊∙ (suc n))))
                (AbGroup→Group ℤ[Fin k ])
  is4 = ΠGroupIso λ _
    → compGroupIso (GroupEquiv→GroupIso (πₙSⁿ≅HⁿSⁿ n))
                    (Hⁿ-Sⁿ≅ℤ n)

πₙ⋁Sⁿ≅ℤ[] : (n k : ℕ)
  → GroupIso (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k)))
              (AbGroup→Group ℤ[Fin k ])
πₙ⋁Sⁿ≅ℤ[] n k =
  compGroupIso
    (GroupEquiv→GroupIso (connectedFun→π'Equiv (suc n)
      (⋁Sphere→ΠSphere , refl) (con k)))
    (πₙΠSⁿ≅ℤ[] (suc n) k)
  where
  con : (k : _)
    → isConnectedFun (suc (suc (suc (suc n)))) (⋁Sphere→ΠSphere {k = k})
  con zero b = ∣ (inl tt) , (funExt λ ()) ∣
    , TR.elim
      (λ _ → isOfHLevelPath _ (isOfHLevelTrunc (suc (suc (suc (suc n))))) _ _)
       λ {((inl tt) , q) → cong ∣_∣ₕ (ΣPathP (refl , cong funExt (funExt λ())))}
  con (suc k) b = isConnectedSubtr (suc (suc (suc (suc n)))) n
           (subst (λ p → isConnected p (fiber ⋁Sphere→ΠSphere b))
             (cong suc (sym (+-suc _ _)) ∙ sym (+-suc _ _))
             (isConnected⋁Sphere→ΠSphere b))

-- Generator of πₙ⋁Sⁿ
genπₙ⋁Sⁿ : {n k : ℕ} (x : Fin k)
  → π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k)) .fst
genπₙ⋁Sⁿ x = ∣ (λ s → inr (x , s)) , (sym (push x)) ∣₂

πₙ⋁Sⁿ≅ℤ[]Generator : (n k : ℕ) (x : Fin k)
  → Iso.fun (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x)
  ≡ ℤFinGenerator x
πₙ⋁Sⁿ≅ℤ[]Generator n k x = funExt pickPetalId
  where
  pickPetalId : (w : _)
    → degree (suc (suc n)) (λ z → ⋁Sphere→ΠSphere (inr (x , z)) w)
    ≡ ℤFinGenerator x w
  pickPetalId w with (fst x ≟ᵗ fst w) | (fst w ≟ᵗ fst x)
  ... | lt x | lt x₁ = degreeConst (suc (suc n))
  ... | lt p | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst w) (sym q) p))
  ... | lt x | gt x₁ = degreeConst (suc (suc n))
  ... | eq p | lt q = ⊥.rec (⊥.rec (¬m<ᵗm (subst (fst w <ᵗ_) p q)))
  ... | eq x | eq x₁ = degreeIdfun (suc (suc n))
  ... | eq p | gt q = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) (sym p) q))
  ... | gt x | lt x₁ = degreeConst (suc (suc n))
  ... | gt p | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) q p))
  ... | gt x | gt x₁ = degreeConst (suc (suc n))

-- Elimination principles for homomorphisms out of πₙ⋁Sⁿ
πₙ⋁SⁿHomElim : {n k k' : ℕ}
  (ϕ ψ : GroupHom (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k)))
                  (AbGroup→Group ℤ[Fin k' ]))
  → ((x  : Fin k) → fst ϕ (genπₙ⋁Sⁿ x) ≡ fst ψ (genπₙ⋁Sⁿ x))
  → ϕ ≡ ψ
πₙ⋁SⁿHomElim {n = n} {k} {k'} ϕ ψ ind =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x
    → cong (fst ϕ) (sym (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x))
    ∙ funExt⁻ (cong fst lem) (Iso.fun (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x)
    ∙ cong (fst ψ) (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x))
  where
  lem : compGroupHom (GroupIso→GroupHom (invGroupIso (πₙ⋁Sⁿ≅ℤ[] n k))) ϕ
      ≡ compGroupHom (GroupIso→GroupHom (invGroupIso (πₙ⋁Sⁿ≅ℤ[] n k))) ψ
  lem = agreeOnℤFinGenerator→≡
    λ x → cong (fst ϕ) (cong (Iso.inv (fst (πₙ⋁Sⁿ≅ℤ[] n k)))
                              (sym (πₙ⋁Sⁿ≅ℤ[]Generator n k x))
                      ∙ Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x))
        ∙ ind x
        ∙ cong (fst ψ) (sym (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x))
                      ∙ sym (cong (Iso.inv (fst (πₙ⋁Sⁿ≅ℤ[] n k)))
                                  (sym (πₙ⋁Sⁿ≅ℤ[]Generator n k x))))
