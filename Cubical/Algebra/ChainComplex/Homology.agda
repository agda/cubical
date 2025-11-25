{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Homology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Finite

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.HITs.PropositionalTruncation as PT


private
  variable
    ℓ ℓ' ℓ'' : Level

open ChainComplexMap
open ChainComplex
open finChainComplexMap
open IsGroupHom

module _ (n : ℕ) (C : ChainComplex ℓ) where
  ker∂n = kerGroup (bdry C n)

  ∂ker : GroupHom (AbGroup→Group (chain C (suc (suc n)))) ker∂n
  ∂ker .fst x = (bdry C (suc n) .fst x) , t
    where
    opaque
     t : ⟨ fst (kerSubgroup (bdry C n)) (bdry C (suc n) .fst x) ⟩
     t = funExt⁻ (cong fst (bdry²=0 C n)) x
  ∂ker .snd = makeIsGroupHom (λ x y → kerGroup≡ (bdry C n) ((bdry C (suc n) .snd .pres· x y)))

  img∂+1⊂ker∂n : NormalSubgroup ker∂n
  fst img∂+1⊂ker∂n = imSubgroup ∂ker
  snd img∂+1⊂ker∂n = isNormalImSubGroup
    where
    opaque
      module C1 = AbGroupStr (chain C (suc n)  .snd)
      isNormalImSubGroup : isNormal (imSubgroup ∂ker)
      isNormalImSubGroup = isNormalIm ∂ker
        (λ x y → kerGroup≡ (bdry C n) (C1.+Comm (fst x) (fst y)))

-- Definition of homology
homology : (n : ℕ) → ChainComplex ℓ → Group ℓ
homology n C = (ker∂n n C) / (img∂+1⊂ker∂n n C)

-- Induced maps on cohomology by finite chain complex maps/homotopies
module _ where
  finChainComplexMap→HomologyMap : {C D : ChainComplex ℓ} (m : ℕ)
    → (ϕ : finChainComplexMap (suc m) C D)
    → (n : Fin m)
    → GroupHom (homology (fst n) C) (homology (fst n) D)
  finChainComplexMap→HomologyMap {C = C} {D} m mp (n , p) = main
    where
    ϕ = fchainmap mp
    ϕcomm = fbdrycomm mp

    lem : (k : ℕ) {p q : _} (f : fst (chain C k))
      → fst (ϕ (k , p)) f ≡ fst (ϕ (k , q)) f
    lem k {p} {q} f i = fst (ϕ (k , pq i)) f
      where
      pq : p ≡ q
      pq = isProp<ᵗ _ _

    fun : homology n C .fst → homology n D .fst
    fun = SQ.elim (λ _ → squash/) f
       λ f g → PT.rec (GroupStr.is-set (homology n D .snd) _ _ )
         λ r → eq/ _ _
           ∣ (ϕ (suc (suc n) , p) .fst (fst r))
           , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
               ((funExt⁻ (cong fst (ϕcomm (suc n , _))) (fst r)
                 ∙∙ cong (fst (ϕ (suc n , _))) (cong fst (snd r))
                 ∙∙ (IsGroupHom.pres· (snd (ϕ (suc n , _) )) _ _
                 ∙ cong₂ (AbGroupStr._+_ (snd (chain D (suc n))))
                         (lem (suc n) (fst f))
                         (IsGroupHom.presinv (snd (ϕ (suc n , _) )) _
                       ∙ cong (snd (chain D (suc n)) .AbGroupStr.-_)
                          (lem (suc n) (fst g)))))) ∣₁
      where
      f : _ → homology n D .fst
      f (a , b) = [ ϕ (suc n , <ᵗ-trans p <ᵗsucm) .fst a
                , ((λ i → fst (ϕcomm (n , <ᵗ-trans p <ᵗsucm)  i) a)
                ∙∙ cong (fst (ϕ (n , _))) b
                ∙∙ IsGroupHom.pres1 (snd (ϕ (n , _)))) ]


    main : GroupHom (homology n C) (homology n D)
    fst main = fun
    snd main =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd (homology n D)) _ _)
          λ a b → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
              (IsGroupHom.pres· (snd (ϕ (suc n , _) )) _ _)))

  finChainComplexMap→HomologyMapComp : {C D E : ChainComplex ℓ} {m : ℕ}
    → (ϕ : finChainComplexMap (suc m) C D) (ψ : finChainComplexMap (suc m) D E)
    → (n : Fin m)
    → finChainComplexMap→HomologyMap m (compFinChainMap ϕ ψ) n
     ≡ compGroupHom (finChainComplexMap→HomologyMap m ϕ n)
                    (finChainComplexMap→HomologyMap m ψ n)
  finChainComplexMap→HomologyMapComp {E = E} _ _ n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (fst n) E)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain E (fst n))) _ _) refl)))

  finChainComplexMap→HomologyMapId : {C : ChainComplex ℓ} {m : ℕ} (n : Fin m)
    → finChainComplexMap→HomologyMap m (idFinChainMap (suc m) C) n ≡ idGroupHom
  finChainComplexMap→HomologyMapId {C = C} n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (fst n) C)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C (fst n))) _ _) refl)))

  finChainComplexEquiv→HomoglogyIso :
    {C D : ChainComplex ℓ} (m : ℕ) (f : C ≃⟨ (suc m) ⟩Chain D)
    → (n : Fin m) → GroupIso (homology (fst n) C) (homology (fst n) D)
  Iso.fun (fst (finChainComplexEquiv→HomoglogyIso m (f , eqs) n)) =
    finChainComplexMap→HomologyMap m f n .fst
  Iso.inv (fst (finChainComplexEquiv→HomoglogyIso m f n)) =
    finChainComplexMap→HomologyMap m (invFinChainMap f) n .fst
  Iso.rightInv (fst (finChainComplexEquiv→HomoglogyIso m (f , eqs) n)) =
    funExt⁻ (cong fst (sym (finChainComplexMap→HomologyMapComp
                             (invFinChainMap (f , eqs)) f n))
           ∙∙  cong (λ f → fst (finChainComplexMap→HomologyMap m f n))
                 (finChainComplexMap≡ λ r
                   →  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (secEq (_ , eqs r))))
           ∙∙ cong fst (finChainComplexMap→HomologyMapId n))
  Iso.leftInv (fst (finChainComplexEquiv→HomoglogyIso m (f , eqs) n)) =
    funExt⁻ (cong fst (sym (finChainComplexMap→HomologyMapComp f
                            (invFinChainMap (f , eqs)) n))
          ∙∙ cong (λ f → fst (finChainComplexMap→HomologyMap m f n))
                  (finChainComplexMap≡
                (λ n → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (retEq (_ , eqs n)))))
          ∙∙ cong fst (finChainComplexMap→HomologyMapId n))
  snd (finChainComplexEquiv→HomoglogyIso m (f , eqs) n) =
    finChainComplexMap→HomologyMap m f n .snd


  finChainHomotopy→HomologyPath : {A B : ChainComplex ℓ} {m : ℕ}
    (f g : finChainComplexMap (suc m) A B)
    → finChainHomotopy (suc m) f g
    → (n : Fin m)
    → finChainComplexMap→HomologyMap m f n
     ≡ finChainComplexMap→HomologyMap m g n
  finChainHomotopy→HomologyPath {A = A} {B = B} {m = m} f g ϕ n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (fst n) _)) _ _)
        λ {(a , p) → eq/ _ _
          ∣ (finChainHomotopy.fhtpy ϕ (suc (fst n) , pf) .fst a)
          , (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain B (fst n)))  _ _)
                    (sym ((funExt⁻ (cong fst (finChainHomotopy.fbdryhtpy ϕ _)) a)
                       ∙ cong₂ _+B_ refl
                                  (cong (fst (finChainHomotopy.fhtpy ϕ _)) p
                                ∙ IsGroupHom.pres1 (snd (finChainHomotopy.fhtpy ϕ _)))
                       ∙ AbGroupStr.+IdR (snd (chain B (suc (fst n)))) _))) ∣₁}))
    where
    open GroupTheory (AbGroup→Group (chain B (suc (fst n))))
    pf : suc (fst n) <ᵗ suc (suc m)
    pf = <ᵗ-trans (snd n) <ᵗsucm

    invB = GroupStr.inv (snd (AbGroup→Group (chain B (suc (fst n)))))
    _+B_ = AbGroupStr._+_ (snd (chain B (suc (fst n))))

-- corresponding lemmas/constructions for full chain complex maps/homotopies
module _ where
  chainComplexMap→HomologyMap : {C D : ChainComplex ℓ}
    → (ϕ : ChainComplexMap C D)
    → (n : ℕ)
    → GroupHom (homology n C) (homology n D)
  chainComplexMap→HomologyMap {C = C} {D} mp n = main
    where
    ϕ = chainmap mp
    ϕcomm = bdrycomm mp
    fun : homology n C .fst → homology n D .fst
    fun = SQ.elim (λ _ → squash/) f
      λ f g → PT.rec (GroupStr.is-set (homology n D .snd) _ _ ) (λ r
      →  eq/ _ _ ∣ (fst (ϕ (suc (suc n))) (fst r))
                , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                         (funExt⁻ (cong fst (ϕcomm (suc n))) (fst r)
                       ∙∙ cong (fst (ϕ (suc n) )) (cong fst (snd r))
                       ∙∙ IsGroupHom.pres· (snd (ϕ (suc n) )) _ _
                        ∙ cong₂ (AbGroupStr._+_ (snd (chain D (suc n) )))
                                refl
                                (IsGroupHom.presinv (snd (ϕ (suc n) )) _)) ∣₁)
      where
      f : _ → homology n D .fst
      f (a , b) = [ (ϕ (suc n)  .fst a)
                , ((λ i → fst (ϕcomm n  i) a)
                ∙∙ cong (fst (ϕ n)) b
                ∙∙ IsGroupHom.pres1 (snd (ϕ n))) ]

    main : GroupHom (homology n C) (homology n D)
    fst main = fun
    snd main =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd (homology n D)) _ _)
          λ a b → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
              (IsGroupHom.pres· (snd (ϕ (suc n) )) _ _)))

  chainComplexMap→HomologyMapComp : {C D E : ChainComplex ℓ}
    → (ϕ : ChainComplexMap C D) (ψ : ChainComplexMap D E)
    → (n : ℕ)
    → chainComplexMap→HomologyMap (compChainMap ϕ ψ) n
     ≡ compGroupHom (chainComplexMap→HomologyMap ϕ n)
                    (chainComplexMap→HomologyMap ψ n)
  chainComplexMap→HomologyMapComp {E = E} _ _ n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n E)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain E n)) _ _) refl)))

  chainComplexMap→HomologyMapId : {C : ChainComplex ℓ} (n : ℕ)
    → chainComplexMap→HomologyMap (idChainMap C) n ≡ idGroupHom
  chainComplexMap→HomologyMapId {C = C} n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n C)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _) refl)))

  ChainHomotopy→HomologyPath : {A B : ChainComplex ℓ} (f g : ChainComplexMap A B)
    → ChainHomotopy f g
    → (n : ℕ) → chainComplexMap→HomologyMap f n
                  ≡ chainComplexMap→HomologyMap g n
  ChainHomotopy→HomologyPath {A = A} {B = B} f g ϕ n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n _)) _ _)
        λ {(a , p) → eq/ _ _
          ∣ (ChainHomotopy.htpy ϕ (suc n) .fst a)
          , (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain B n))  _ _)
                  (sym ((funExt⁻ (cong fst (ChainHomotopy.bdryhtpy ϕ n)) a)
                     ∙ cong₂ _+B_ refl
                                (cong (fst (ChainHomotopy.htpy ϕ n)) p
                              ∙ IsGroupHom.pres1 (snd (ChainHomotopy.htpy ϕ n)))
                     ∙ AbGroupStr.+IdR (snd (chain B (suc n))) _))) ∣₁}))
    where
    open GroupTheory (AbGroup→Group (chain B (suc n)))
    invB = GroupStr.inv (snd (AbGroup→Group (chain B (suc n))))
    _+B_ = AbGroupStr._+_ (snd (chain B (suc n)))

  chainComplexEquiv→HomoglogyIso : {C D : ChainComplex ℓ} (f : C ≃Chain D)
    → (n : ℕ) → GroupIso (homology n C) (homology n D)
  Iso.fun (fst (chainComplexEquiv→HomoglogyIso (f , eqs) n)) =
    chainComplexMap→HomologyMap f n .fst
  Iso.inv (fst (chainComplexEquiv→HomoglogyIso (f , eqs) n)) =
    chainComplexMap→HomologyMap (invChainMap (f , eqs)) n .fst
  Iso.rightInv (fst (chainComplexEquiv→HomoglogyIso (f , eqs) n)) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp
                             (invChainMap (f , eqs)) f n))
           ∙∙  cong (λ f → fst (chainComplexMap→HomologyMap f n))
                 (ChainComplexMap≡ λ r
                   →  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (secEq (_ , eqs r))))
           ∙∙ cong fst (chainComplexMap→HomologyMapId n))

  Iso.leftInv (fst (chainComplexEquiv→HomoglogyIso (f , eqs) n)) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp f
                            (invChainMap (f , eqs)) n))
          ∙∙ cong (λ f → fst (chainComplexMap→HomologyMap f n))
                  (ChainComplexMap≡
                (λ n → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (retEq (_ , eqs n)))))
          ∙∙ cong fst (chainComplexMap→HomologyMapId n))
  snd (chainComplexEquiv→HomoglogyIso (f , eqs) n) =
    chainComplexMap→HomologyMap f n .snd

-- More general version
homologyIso : (n : ℕ) (C D : ChainComplex ℓ)
  → (chEq₂ : AbGroupIso (chain C (suc (suc n)))
                         (chain D (suc (suc n))))
  → (chEq₁ : AbGroupIso (chain C (suc n))
                         (chain D (suc n)))
  → (chEq₀ : AbGroupIso (chain C n)
                         (chain D n))
  → Iso.fun (chEq₀ .fst) ∘ bdry C n .fst
   ≡ bdry D n .fst ∘ Iso.fun (chEq₁ .fst)
  → Iso.fun (chEq₁ .fst) ∘ bdry C (suc n) .fst
   ≡ bdry D (suc n) .fst ∘ Iso.fun (chEq₂ .fst)
  → GroupIso (homology n C) (homology n D)
homologyIso n C D chEq₂ chEq₁ chEq₀ eq1 eq2 = main-iso
  where
  F : homology n C .fst → homology n D .fst
  F = SQ.elim (λ _ → squash/) f
    λ a b r → eq/ _ _
      (PT.map (λ { (s , t)
        → (Iso.fun (chEq₂ .fst) s)
          , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
            (sym (funExt⁻ eq2 s)
           ∙ cong (Iso.fun (chEq₁ .fst)) (cong fst t)
           ∙ IsGroupHom.pres· (chEq₁ .snd) _ _
           ∙ cong₂ (snd (chain D (suc n) ) .AbGroupStr._+_)
                   refl
                   (IsGroupHom.presinv (chEq₁ .snd) _))}) r)
    where
    f : _ → homology n D .fst
    f (a , b) = [ Iso.fun (fst chEq₁) a
                , sym (funExt⁻ eq1 a) ∙ cong (Iso.fun (chEq₀ .fst)) b
                ∙ IsGroupHom.pres1 (snd chEq₀) ]

  G : homology n D .fst → homology n C .fst
  G = SQ.elim (λ _ → squash/) g
    λ a b r → eq/ _ _
      (PT.map (λ {(s , t)
      → (Iso.inv (chEq₂ .fst) s)
       , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _)
           (sym (Iso.leftInv (chEq₁ .fst) _)
          ∙ cong (Iso.inv (chEq₁ .fst)) (funExt⁻ eq2 (Iso.inv (chEq₂ .fst) s))
          ∙ cong (Iso.inv (chEq₁ .fst) ∘ bdry D (suc n) .fst)
                 (Iso.rightInv (chEq₂ .fst) s)
          ∙ cong (Iso.inv (chEq₁ .fst)) (cong fst t)
          ∙ IsGroupHom.pres· (invGroupIso chEq₁ .snd) _ _
          ∙ cong₂ (snd (chain C (suc n) ) .AbGroupStr._+_)
                   refl
                   ((IsGroupHom.presinv (invGroupIso chEq₁ .snd) _)))}) r)
    where
    g : _ → homology n C .fst
    g (a , b) = [ Iso.inv (fst chEq₁) a
                , sym (Iso.leftInv (chEq₀ .fst) _)
                ∙ cong (Iso.inv (chEq₀ .fst)) (funExt⁻ eq1 (Iso.inv (chEq₁ .fst) a))
                ∙ cong (Iso.inv (chEq₀ .fst) ∘ bdry D n  .fst)
                       (Iso.rightInv (chEq₁ .fst) a)
                ∙ cong (Iso.inv (chEq₀ .fst)) b
                ∙ IsGroupHom.pres1 (invGroupIso chEq₀ .snd) ]

  F-hom : IsGroupHom (homology n C .snd) F (homology n D .snd)
  F-hom =
    makeIsGroupHom
      (SQ.elimProp2 (λ _ _ → GroupStr.is-set (homology n D .snd) _ _)
        λ {(a , s) (b , t)
        → cong [_] (Σ≡Prop (λ _
          → AbGroupStr.is-set (snd (chain D n)) _ _)
                     (IsGroupHom.pres·  (snd chEq₁) _ _)) })

  main-iso : GroupIso (homology n C) (homology n D)
  Iso.fun (fst main-iso) = F
  Iso.inv (fst main-iso) = G
  Iso.rightInv (fst main-iso) =
    elimProp (λ _ → GroupStr.is-set (homology n D .snd) _ _)
      λ{(a , b)
      → cong [_] (Σ≡Prop (λ _
        → AbGroupStr.is-set (snd (chain D n)) _ _)
                  (Iso.rightInv (fst chEq₁) a))}
  Iso.leftInv (fst main-iso) =
    elimProp (λ _ → GroupStr.is-set (homology n C .snd) _ _)
      λ{(a , b)
      → cong [_] (Σ≡Prop (λ _
        → AbGroupStr.is-set (snd (chain C n)) _ _)
                  (Iso.leftInv (fst chEq₁) a))}
  snd main-iso = F-hom
