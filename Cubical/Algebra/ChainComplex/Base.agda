{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Base where
{-
  Defines groups and adds the smart constructors [makeGroup-right] and [makeGroup-left]
  for constructing groups from less data than the standard [makeGroup] constructor.
-}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties -- TODO: why is this there and not exported by the Morphisms file?
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Structures.Successor

private
  variable
    ℓ ℓ' ℓ'' : Level

module CC {ℓ₀ : Level} (I : SuccStr ℓ₀) where
  open SuccStr I
  record ChainComplex (ℓ : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ₀)) where
    field
      chain   : (i : Index) → AbGroup ℓ
      bdry    : (i : Index) → AbGroupHom (chain (succ i)) (chain i)
      bdry²=0 : (i : Index) → compGroupHom (bdry (succ i)) (bdry i) ≡ trivGroupHom

  record ChainComplexMap {ℓ ℓ' : Level}
   (A : ChainComplex ℓ) (B : ChainComplex ℓ') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀) where
    open ChainComplex
    field
      chainmap : (i : Index) → AbGroupHom (chain A i) (chain B i)
      bdrycomm : (i : Index) → compGroupHom (chainmap (succ i)) (bdry B i)
                           ≡ compGroupHom (bdry A i) (chainmap i)

  record ChainHomotopy {ℓ : Level} {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    (f g : ChainComplexMap A B) : Type (ℓ-max (ℓ-max ℓ' ℓ) ℓ₀) where
    open ChainComplex
    open ChainComplexMap
    field
      htpy : (i : Index) → AbGroupHom (chain A i) (chain B (succ i))
      bdryhtpy : (i : Index)
        → subtrGroupHom (chain A (succ i)) (chain B (succ i))
                         (chainmap f (succ i)) (chainmap g (succ i))
         ≡ addGroupHom (chain A (succ i)) (chain B (succ i))
             (compGroupHom (htpy (succ i)) (bdry B (succ i)))
             (compGroupHom (bdry A i) (htpy i))

  record CoChainComplex (ℓ : Level) : Type (ℓ-max (ℓ-suc ℓ) ℓ₀) where
    field
      cochain   : (i : Index) → AbGroup ℓ
      cobdry    : (i : Index) → AbGroupHom (cochain i) (cochain (succ i))
      cobdry²=0 : (i : Index) → compGroupHom (cobdry i) (cobdry (succ i))
                               ≡ trivGroupHom

  open ChainComplexMap


  ChainComplexMap≡ : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    {f g : ChainComplexMap A B}
    → ((i : Index) → chainmap f i ≡ chainmap g i)
    → f ≡ g
  chainmap (ChainComplexMap≡ p i) n = p n i
  bdrycomm (ChainComplexMap≡ {A = A} {B = B} {f = f} {g = g} p i) n =
    isProp→PathP {B = λ i → compGroupHom (p (succ n) i) (ChainComplex.bdry B n)
                            ≡ compGroupHom (ChainComplex.bdry A n) (p n i)}
        (λ i → isSetGroupHom _ _)
        (bdrycomm f n) (bdrycomm g n) i

  compChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {C : ChainComplex ℓ''}
    → (f : ChainComplexMap A B) (g : ChainComplexMap B C)
    → ChainComplexMap A C
  compChainMap {A = A} {B} {C}
    record { chainmap = ϕ ; bdrycomm = commϕ }
    record { chainmap = ψ ; bdrycomm = commψ } = main
    where
    main : ChainComplexMap A C
    chainmap main n = compGroupHom (ϕ n) (ψ n)
    bdrycomm main n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
             (funExt λ x
             → (funExt⁻ (cong fst (commψ n)) (ϕ (succ n) .fst x))
              ∙ cong (fst (ψ n)) (funExt⁻ (cong fst (commϕ n)) x))

  isChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → ChainComplexMap A B  → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀)
  isChainEquiv f = ((n : Index) → isEquiv (chainmap f n .fst))

  _≃Chain_ : (A : ChainComplex ℓ) (B : ChainComplex ℓ') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀)
  A ≃Chain B = Σ[ f ∈ ChainComplexMap A B ] (isChainEquiv f)

  idChainMap : (A : ChainComplex ℓ) → ChainComplexMap A A
  chainmap (idChainMap A) _ = idGroupHom
  bdrycomm (idChainMap A) _ =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

  invChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → (A ≃Chain B) → ChainComplexMap B A
  chainmap (invChainMap (record { chainmap = ϕ ; bdrycomm = ϕcomm } , eq)) n =
    GroupEquiv→GroupHom (invGroupEquiv ((ϕ n .fst , eq n) , snd (ϕ n)))
  bdrycomm (invChainMap {B = B} (record { chainmap = ϕ ; bdrycomm = ϕcomm } , eq)) n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ x
        → sym (retEq (_ , eq n) _)
        ∙∙ cong (invEq (_ , eq n))
                (sym (funExt⁻ (cong fst (ϕcomm n)) (invEq (_ , eq (succ n)) x)))
        ∙∙ cong (invEq (ϕ n .fst , eq n) ∘ fst (ChainComplex.bdry B n))
                (secEq (_ , eq (succ n)) x))

  invChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → A ≃Chain B → B ≃Chain A
  fst (invChainEquiv e) = invChainMap e
  snd (invChainEquiv e) n = snd (invEquiv (chainmap (fst e) n .fst , snd e n))

  -- TODO: upstream these
  module _ {G H : Group ℓ} (ϕ : GroupHom G H) where
    kerGroup : Group ℓ
    kerGroup = Subgroup→Group G (kerSubgroup ϕ)

    kerGroup≡ : {x y : ⟨ kerGroup ⟩} → x .fst ≡ y .fst → x ≡ y
    kerGroup≡ = Σ≡Prop (isPropIsInKer ϕ)

  open ChainComplex
  open IsGroupHom

  homology : (n : Index) → ChainComplex ℓ → Group ℓ
  homology n C = ker∂n / img∂+1⊂ker∂n
    where
    Cn+2 = AbGroup→Group (chain C (succ (succ n)))
    ∂n = bdry C n
    ∂n+1 = bdry C (succ n)
    ker∂n = kerGroup ∂n

    -- Restrict ∂n+1 to ker∂n
    ∂'-fun : Cn+2 .fst → ker∂n .fst
    fst (∂'-fun x) = ∂n+1 .fst x
    snd (∂'-fun x) = t
      where
      opaque
       t : ⟨ fst (kerSubgroup ∂n) (∂n+1 .fst x) ⟩
       t = funExt⁻ (cong fst (bdry²=0 C n)) x

    ∂' : GroupHom Cn+2 ker∂n
    fst ∂' = ∂'-fun
    snd ∂' = isHom
      where
      opaque
        isHom : IsGroupHom (Cn+2 .snd) ∂'-fun (ker∂n .snd)
        isHom = makeIsGroupHom λ x y
          → kerGroup≡ ∂n (∂n+1 .snd .pres· x y)

    img∂+1⊂ker∂n : NormalSubgroup ker∂n
    fst img∂+1⊂ker∂n = imSubgroup ∂'
    snd img∂+1⊂ker∂n = isNormalImSubGroup
      where
      opaque
        module C1 = AbGroupStr (chain C (succ n) .snd)
        isNormalImSubGroup : isNormal (imSubgroup ∂')
        isNormalImSubGroup = isNormalIm ∂'
          (λ x y → kerGroup≡ ∂n (C1.+Comm (fst x) (fst y)))

  -- ChainComplexMap→finiteChainComplexMap : {C D : ChainComplex ℓ}
  --   → (n : ℕ) → ChainComplexMap C D → finiteChainComplexMap n C D
  -- finchainmap (ChainComplexMap→finiteChainComplexMap n
  --   record { chainmap = chainmap ; bdrycomm = bdrycomm }) m _ = chainmap m
  -- finbdrycomm (ChainComplexMap→finiteChainComplexMap n
  --   record { chainmap = chainmap ; bdrycomm = bdrycomm }) m _ = bdrycomm m

  chainComplexMap→HomologyMap : {C D : ChainComplex ℓ}
    → (ϕ : ChainComplexMap C D)
    → (n : Index)
    → GroupHom (homology n C) (homology n D)
  chainComplexMap→HomologyMap {C = C} {D}
    record { chainmap = ϕ ; bdrycomm = ϕcomm } n = main
    where
    fun : homology n C .fst → homology n D .fst
    fun = SQ.elim (λ _ → squash/) f
      λ f g → PT.rec (GroupStr.is-set (homology n D .snd) _ _ ) (λ r
      →  eq/ _ _ ∣ (fst (ϕ (succ (succ n))) (fst r))
                , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                         (funExt⁻ (cong fst (ϕcomm (succ n))) (fst r)
                       ∙∙ cong (fst (ϕ (succ n))) (cong fst (snd r))
                       ∙∙ IsGroupHom.pres· (snd (ϕ (succ n))) _ _
                        ∙ cong₂ (AbGroupStr._+_ (snd (chain D (succ n))))
                                refl
                                (IsGroupHom.presinv (snd (ϕ (succ n))) _)) ∣₁)
      where
      f : _ → homology n D .fst
      f (a , b) = [ (ϕ (succ n) .fst a)
                , ((λ i → fst (ϕcomm n i) a)
                ∙∙ cong (fst (ϕ n)) b
                ∙∙ IsGroupHom.pres1 (snd (ϕ n))) ]

    main : GroupHom (homology n C) (homology n D)
    fst main = fun
    snd main =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd (homology n D)) _ _)
          λ a b → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
              (IsGroupHom.pres· (snd (ϕ (succ n))) _ _)))

  -- chainComplexMap→HomologyMap : {C D : ChainComplex ℓ}
  --   → (ϕ : ChainComplexMap C D)
  --   → (n : ℕ)
  --   → GroupHom (homology n C) (homology n D)
  -- chainComplexMap→HomologyMap {C = C} {D} ϕ n =
  --   finiteChainComplexMap→HomologyMap n (suc (suc n)) (0 , refl)
  --     (ChainComplexMap→finiteChainComplexMap (suc (suc n)) ϕ)

  chainComplexMap→HomologyMapComp : {C D E : ChainComplex ℓ}
    → (ϕ : ChainComplexMap C D) (ψ : ChainComplexMap D E)
    → (n : Index)
    → chainComplexMap→HomologyMap (compChainMap ϕ ψ) n
     ≡ compGroupHom (chainComplexMap→HomologyMap ϕ n)
                    (chainComplexMap→HomologyMap ψ n)
  chainComplexMap→HomologyMapComp {E = E}
    record { chainmap = ϕ ; bdrycomm = commϕ }
    record { chainmap = ψ ; bdrycomm = commψ } n =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n E)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain E n)) _ _) refl)))

  chainComplexMap→HomologyMapId : {C : ChainComplex ℓ} (n : Index)
    → chainComplexMap→HomologyMap (idChainMap C) n ≡ idGroupHom
  chainComplexMap→HomologyMapId {C = C} n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n C)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _) refl)))

  ChainHomotopy→HomologyPath : {A B : ChainComplex ℓ} (f g : ChainComplexMap A B)
    → ChainHomotopy f g
    → (n : Index) → chainComplexMap→HomologyMap f n
                ≡ chainComplexMap→HomologyMap g n
  ChainHomotopy→HomologyPath {A = A} {B = B} f g ϕ n =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology n _)) _ _)
        λ {(a , p) → eq/ _ _
          ∣ (ChainHomotopy.htpy ϕ (succ n) .fst a)
          , (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain B n))  _ _)
                    (sym ((funExt⁻ (cong fst (ChainHomotopy.bdryhtpy ϕ n)) a)
                       ∙ cong₂ _+B_ refl
                                  (cong (fst (ChainHomotopy.htpy ϕ n)) p
                                ∙ IsGroupHom.pres1 (snd (ChainHomotopy.htpy ϕ n)))
                       ∙ AbGroupStr.+IdR (snd (chain B (succ n))) _))) ∣₁}))
    where
    open GroupTheory (AbGroup→Group (chain B (succ n)))
    invB = GroupStr.inv (snd (AbGroup→Group (chain B (succ n))))
    _+B_ = AbGroupStr._+_ (snd (chain B (succ n)))

  chainComplexEquiv→HomoglogyIso : {C D : ChainComplex ℓ} (f : C ≃Chain D)
    → (n : Index) → GroupIso (homology n C) (homology n D)
  Iso.fun (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    chainComplexMap→HomologyMap f n .fst
  Iso.inv (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    chainComplexMap→HomologyMap (invChainMap (f , eq)) n .fst
  Iso.rightInv (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp
                             (invChainMap (f , eq)) f n))
          ∙∙ cong (λ f → fst (chainComplexMap→HomologyMap f n))
              (ChainComplexMap≡
                (λ n → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (secEq (_ , eq n)))))
          ∙∙ cong fst (chainComplexMap→HomologyMapId n))
  Iso.leftInv (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp f
                            (invChainMap (f , eq)) n))
          ∙∙ cong (λ f → fst (chainComplexMap→HomologyMap f n))
                  (ChainComplexMap≡
                (λ n → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (retEq (_ , eq n)))))
          ∙∙ cong fst (chainComplexMap→HomologyMapId n))
  snd (chainComplexEquiv→HomoglogyIso (f , eq) n) =
    chainComplexMap→HomologyMap f n .snd

  -- More general version
  homologyIso : (n : Index) (C D : ChainComplex ℓ)
    → (chEq₂ : AbGroupIso (chain C (succ (succ n))) (chain D (succ (succ n))))
    → (chEq₁ : AbGroupIso (chain C (succ n)) (chain D (succ n)))
    → (chEq₀ : AbGroupIso (chain C n) (chain D n))
    → Iso.fun (chEq₀ .fst) ∘ bdry C n .fst
     ≡ bdry D n .fst ∘ Iso.fun (chEq₁ .fst)
    → Iso.fun (chEq₁ .fst) ∘ bdry C (succ n) .fst
     ≡ bdry D (succ n) .fst ∘ Iso.fun (chEq₂ .fst)
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
             ∙ cong₂ (snd (chain D (succ n)) .AbGroupStr._+_)
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
            ∙ cong (Iso.inv (chEq₁ .fst) ∘ bdry D (succ n) .fst)
                   (Iso.rightInv (chEq₂ .fst) s)
            ∙ cong (Iso.inv (chEq₁ .fst)) (cong fst t)
            ∙ IsGroupHom.pres· (invGroupIso chEq₁ .snd) _ _
            ∙ cong₂ (snd (chain C (succ n)) .AbGroupStr._+_)
                     refl
                     ((IsGroupHom.presinv (invGroupIso chEq₁ .snd) _)))}) r)
      where
      g : _ → homology n C .fst
      g (a , b) = [ Iso.inv (fst chEq₁) a
                  , sym (Iso.leftInv (chEq₀ .fst) _)
                  ∙ cong (Iso.inv (chEq₀ .fst)) (funExt⁻ eq1 (Iso.inv (chEq₁ .fst) a))
                  ∙ cong (Iso.inv (chEq₀ .fst) ∘ bdry D n .fst)
                         (Iso.rightInv (chEq₁ .fst) a)
                  ∙ cong (Iso.inv (chEq₀ .fst)) b
                  ∙ IsGroupHom.pres1 (invGroupIso chEq₀ .snd) ]

    F-hom : IsGroupHom (homology n C .snd) F (homology n D .snd)
    F-hom =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (homology n D .snd) _ _)
          λ {(a , s) (b , t)
          → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                       (IsGroupHom.pres·  (snd chEq₁) _ _)) })

    main-iso : GroupIso (homology n C) (homology n D)
    Iso.fun (fst main-iso) = F
    Iso.inv (fst main-iso) = G
    Iso.rightInv (fst main-iso) =
      elimProp (λ _ → GroupStr.is-set (homology n D .snd) _ _)
        λ{(a , b)
        → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                    (Iso.rightInv (fst chEq₁) a))}
    Iso.leftInv (fst main-iso) =
      elimProp (λ _ → GroupStr.is-set (homology n C .snd) _ _)
        λ{(a , b)
        → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _)
                    (Iso.leftInv (fst chEq₁) a))}
    snd main-iso = F-hom
