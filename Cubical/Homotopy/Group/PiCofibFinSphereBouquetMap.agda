{-# OPTIONS --lossy-unification #-}
{-
This file computes πₙ(cofib α) for n ≥ 2 and α : ⋁Sⁿ →∙ ⋁Sⁿ
-}
module Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int
open import Cubical.Data.Unit

open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.IsomorphismTheorems
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB
open import Cubical.Algebra.AbGroup.FinitePresentation

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Group.PiSphereBouquet
open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Connected

open import Cubical.Relation.Nullary

open FinitePresentation

module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc (suc n)) (Fin m)
   →∙ SphereBouquet∙ (suc (suc n)) (Fin k)) where

  BouquetDegreeSubGroup : Subgroup (AbGroup→Group ℤ[Fin k ])
  BouquetDegreeSubGroup = imSubgroup (bouquetDegree (fst α))

  BouquetDegreeNormalSubGroup : NormalSubgroup (AbGroup→Group ℤ[Fin k ])
  fst BouquetDegreeNormalSubGroup = BouquetDegreeSubGroup
  snd BouquetDegreeNormalSubGroup =
    isNormalIm _ λ f g i x → +Comm (f x) (g x) i

  ℤ[]/BouquetDegree : Group ℓ-zero
  ℤ[]/BouquetDegree = AbGroup→Group ℤ[Fin k ] / BouquetDegreeNormalSubGroup


module πCofibFinSphereBouquetMap (n k m : ℕ)
  (α : SphereBouquet∙ (suc (suc n)) (Fin m)
   →∙ SphereBouquet∙ (suc (suc n)) (Fin k)) where

  inr' : SphereBouquet∙ (suc (suc n)) (Fin k) →∙ (cofib (fst α) , inl tt)
  fst inr' = inr
  snd inr' = (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))

  conα : isConnectedFun (suc (suc n)) (fst α)
  conα b =
    isOfHLevelRetractFromIso 0
      (compIso (truncOfΣIso (suc (suc n)))
        (mapCompIso (compIso (Σ-cong-iso-snd
          (λ _ → equivToIso (isContr→≃Unit
            (isConnectedPath (suc (suc n))
              (isConnectedSphereBouquet' {n = suc n}) _ _)))) rUnit×Iso)))
              (isConnectedSubtr (suc (suc n)) 1 isConnectedSphereBouquet')

  coninr : isConnectedFun (suc (suc (suc n))) (fst inr')
  coninr = inrConnected (suc (suc (suc n))) _ _
    (isConnected→isConnectedFun (suc (suc (suc n)))
      isConnectedSphereBouquet')

  open BlakersMassey□ (λ _ → tt) (fst α) (suc (suc n)) (suc n)
    (isConnected→isConnectedFun _ (isConnectedSphereBouquet' {n = suc n}))
    conα

  α∘inr : SphereBouquet∙ (suc (suc n)) (Fin m)
      →∙ (fiber (fst inr') (inl tt) , (inl tt) , inr' .snd)
  fst α∘inr x = (fst α x) , sym (push x)
  snd α∘inr = ΣPathP ((snd α)
          , (compPath-filler' (λ i → inr (α .snd (~ i))) (sym (push (inl tt)))))

  open π'LES inr'
  isSurjective-π'∘∙Hom : isSurjective (π'∘∙Hom (suc n) α∘inr)
  isSurjective-π'∘∙Hom =
    connectedFun→π'Surj (suc n) _
      λ b → isConnectedSubtr' n (suc (suc (suc n)))
        (subst (λ n → isConnected (suc (suc n)) (fiber (fst α∘inr) b))
               (+-suc n n) (lem b))
    where
    is1 : Iso (Σ (Unit × fst (SphereBouquet∙ (suc (suc n)) (Fin k)))
                 PushoutPath×)
              (fiber (fst inr') (inl tt))
    Iso.fun is1 ((tt , s) , p) = s , (sym p)
    Iso.inv is1 (s , p) = (tt , s) , sym p
    Iso.rightInv is1 (s , p) = refl
    Iso.leftInv is1 ((tt , s) , p) = refl

    lem : isConnectedFun (suc (suc n +ℕ suc n)) (α∘inr .fst)
    lem = isConnectedComp _ _ _ (isEquiv→isConnected _ (isoToIsEquiv is1) _)
             isConnected-toPullback

  isSurjective-π'∘∙Hominr : isSurjective (π'∘∙Hom (suc n) inr')
  isSurjective-π'∘∙Hominr = connectedFun→π'Surj (suc n) _ coninr

  Imα⊂Kerinr : (x : _) → isInIm (π'∘∙Hom (suc n) α) x
                        → isInKer (π'∘∙Hom (suc n) inr') x
  Imα⊂Kerinr x p = Im-fib→A⊂Ker-A→B (suc n) x
    (PT.rec squash₁
     (uncurry (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
      (λ a → J (λ x _ → isInIm (fib→A (suc n)) x)
        ∣ (π'∘∙Hom (suc n) α∘inr .fst ∣ a ∣₂)
        , (cong ∣_∣₂ (ΣPathP (refl , (sym (rUnit _)
        ∙ cong-∙ fst (ΣPathP ((cong (fst α) (snd a))
                    , λ i j → push (snd a i) (~ j))) _)))) ∣₁))) p)

  Kerinr⊂Imα : (x : _) → isInKer (π'∘∙Hom (suc n) inr') x
    → isInIm (π'∘∙Hom (suc n) α) x
  Kerinr⊂Imα x p =
    PT.rec squash₁
      (uncurry ( λ f → J (λ x _ → isInIm (π'∘∙Hom (suc n) α) x)
          (PT.rec squash₁ (uncurry
            (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
              (λ g s → ∣ ∣ g ∣₂ , cong ∣_∣₂
                (ΣPathP (refl
                  , sym (cong-∙ fst (ΣPathP ((cong (fst α) (snd g))
                    , (λ i j → push (snd g i) (~ j)))) _) ∙ rUnit _))
                ∙ cong (fib→A (suc n) .fst) s ∣₁))) (isSurjective-π'∘∙Hom f))))
      (Ker-A→B⊂Im-fib→A (suc n) x p)

  -- πₙCofib≅πₙ⋁Sⁿ/ker(πₙinr)
  Iso1 : GroupIso (π'Gr (suc n) (cofib (fst α) , inl tt))
                  (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / kerNormalSubgroup (π'∘∙Hom (suc n) inr'))
  Iso1 =
    compGroupIso (invGroupIso (surjImIso (π'∘∙Hom (suc n) inr')
                              isSurjective-π'∘∙Hominr))
                 (isoThm1 _)

  -- πₙ⋁Sⁿ/ker(πₙinr)≅πₙ⋁Sⁿ/im(πₙα)
  Iso2 : GroupIso (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / kerNormalSubgroup (π'∘∙Hom (suc n) inr'))
                  (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / imNormalSubgroup (π'∘∙Hom (suc n) α) (π'-comm n))
  Iso2 = Hom/Iso idGroupIso (λ a b → Kerinr⊂Imα _) λ a b → Imα⊂Kerinr _

  -- πₙ⋁Sⁿ/im(πₙα)≅ℤ[]/BouquetDegree-α
  Iso3 : GroupIso ((π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / imNormalSubgroup (π'∘∙Hom (suc n) α) (π'-comm n)))
                  (ℤ[]/BouquetDegree α)
  Iso3 = (Hom/ImIso _ _ ( (πₙ⋁Sⁿ≅ℤ[] n m)) ( (πₙ⋁Sⁿ≅ℤ[] n k))
          (funExt⁻ (cong fst (πₙ⋁SⁿHomElim ϕ ψ
            λ s → funExt (λ x
            → sumFinℤId m (λ r → sym (degreeComp' (suc (suc n)) _ _))
             ∙ sumFin-choose  _+_ 0 (λ _ → refl) +Comm _ _ s
               (cong (degree (suc (suc n)))
                 (funExt (λ w → cong (pickPetal x ∘ fst α ∘ inr)
                                   (ΣPathP (refl , lem1 s w)))))
               (λ w p → cong (degree (suc (suc n)))
                   (funExt (λ r → cong (pickPetal x ∘ fst α) (lem2 s x w r p)
                                ∙ (cong (pickPetal x) (snd α))))
                 ∙ degreeConst (suc (suc n)))
             ∙ cong (degree (suc (suc n))) refl)))))
      where
      lem1 : (s : Fin m) (w : S₊ (suc (suc n))) → pickPetal s (inr (s , w)) ≡ w
      lem1 s w with (fst s ≟ᵗ fst s)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq x = refl
      ... | gt x = ⊥.rec (¬m<ᵗm x)

      ϕ = compGroupHom (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n m)) (bouquetDegree (fst α))
      ψ = compGroupHom (π'∘∙Hom (suc n) α) ((GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)))

      lem2 : (s : Fin m) (x : Fin k) (w : Fin m) (r : Susp (S₊ (suc n)))
        (p : ¬ w ≡ s)
        → Path (SphereBouquet (suc (suc n)) (Fin m))
               (inr (w , ⋁Sphere→ΠSphere (inr (s , r)) w)) (inl tt)
      lem2 s x w r p with (fst w ≟ᵗ fst s)
      ... | lt x₁ = sym (push w)
      ... | eq x₁ = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) x₁))
      ... | gt x₁ = sym (push w)


-- Main results
π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree : {n m k : ℕ}
  (α : SphereBouquet∙ (suc (suc n)) (Fin m)
   →∙ SphereBouquet∙ (suc (suc n)) (Fin k))
  → GroupIso (π'Gr (suc n) (cofib (fst α) , inl tt))
              (ℤ[]/BouquetDegree α)
π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree {n = n} {m} {k} α =
  compGroupIso (compGroupIso (πCofibFinSphereBouquetMap.Iso1 n k m α)
                             (πCofibFinSphereBouquetMap.Iso2 n k m α))
                             (πCofibFinSphereBouquetMap.Iso3 n k m α)

hasFPπ'CofibFinSphereBouquetMap : {n m k : ℕ}
  (α : FinSphereBouquetMap∙ m k (suc n))
  → FinitePresentation (Group→AbGroup (π'Gr (suc n) (cofib (fst α) , inl tt))
                                       (π'-comm n))
nGens (hasFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) = k
nRels (hasFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) = m
rels (hasFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) =
  bouquetDegree (fst α)
fpiso (hasFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) =
  π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α
