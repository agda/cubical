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
open import Cubical.Relation.Nullary


private
  variable
    ℓ ℓ' ℓ'' : Level

module CC {ℓ₀ : Level} (I : InjSuccStr ℓ₀) where
  open InjSuccStr I
  open SuccStr succStr

  ≠succ : Index → Type ℓ₀
  ≠succ i = ¬ (i ≡ succ i)

  Index⇃ : Type ℓ₀
  Index⇃ = Σ[ i ∈ Index ] (≠succ (succ (succ i)))

  record ChainComplex (ℓ : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ₀)) where
    field
      chain   : (i : Index) → ≠succ i → AbGroup ℓ
      bdry    : (i : Index) (p : ≠succ (succ i)) → AbGroupHom (chain (succ i) p) (chain i (semiInj p))
      bdry²=0 : (i : Index) (p : ≠succ (succ (succ i)))
        → compGroupHom (bdry (succ i) p) (bdry i (semiInj p)) ≡ trivGroupHom

  record ChainComplexMap {ℓ ℓ' : Level}
   (A : ChainComplex ℓ) (B : ChainComplex ℓ') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀) where
    open ChainComplex
    field
      chainmap : (i : Index) (p : ≠succ i) → AbGroupHom (chain A i p) (chain B i p)
      bdrycomm : (i : Index) (p : ≠succ (succ i))
        → compGroupHom (chainmap (succ i) p) (bdry B i p)
         ≡ compGroupHom (bdry A i p) (chainmap i (semiInj p))

  record ChainHomotopy {ℓ : Level} {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    (f g : ChainComplexMap A B) : Type (ℓ-max (ℓ-max ℓ' ℓ) ℓ₀) where
    open ChainComplex
    open ChainComplexMap
    field
      htpy : (i : Index) (p : ≠succ (succ i)) → AbGroupHom (chain A i (semiInj p)) (chain B (succ i) p)
      bdryhtpy : (i : Index) (p : ≠succ (succ (succ i)))
        → subtrGroupHom (chain A (succ i) (semiInj p)) (chain B (succ i) (semiInj p))
                         (chainmap f (succ i) (semiInj p)) (chainmap g (succ i)(semiInj p))
         ≡ addGroupHom (chain A (succ i) (semiInj p)) (chain B (succ i) (semiInj p))
             (compGroupHom (htpy (succ i) p) (bdry B (succ i) p))
             (compGroupHom (bdry A i (semiInj p)) (htpy i (semiInj p)))

  record CoChainComplex (ℓ : Level) : Type (ℓ-max (ℓ-suc ℓ) ℓ₀) where
    field
      cochain   : (i : Index) → AbGroup ℓ
      cobdry    : (i : Index) → AbGroupHom (cochain i) (cochain (succ i))
      cobdry²=0 : (i : Index) → compGroupHom (cobdry i) (cobdry (succ i))
                               ≡ trivGroupHom

  open ChainComplexMap


  ChainComplexMap≡ : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    {f g : ChainComplexMap A B}
    → ((i : Index) (j : _) → chainmap f i j ≡ chainmap g i j)
    → f ≡ g
  chainmap (ChainComplexMap≡ p i) n j = p n j i
  bdrycomm (ChainComplexMap≡ {A = A} {B = B} {f = f} {g = g} p i) n r =
    isProp→PathP {B = λ i → compGroupHom (p (succ n) r i) (ChainComplex.bdry B n r)
                            ≡ compGroupHom (ChainComplex.bdry A n r) (p n (semiInj r) i)}
        (λ i → isSetGroupHom _ _)
        (bdrycomm f n r) (bdrycomm g n r) i

  compChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'} {C : ChainComplex ℓ''}
    → (f : ChainComplexMap A B) (g : ChainComplexMap B C)
    → ChainComplexMap A C
  compChainMap {A = A} {B} {C}
    record { chainmap = ϕ ; bdrycomm = commϕ }
    record { chainmap = ψ ; bdrycomm = commψ } = main
    where
    main : ChainComplexMap A C
    chainmap main n r = compGroupHom (ϕ n r) (ψ n r)
    bdrycomm main n r =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
             (funExt λ x
             → (funExt⁻ (cong fst (commψ n r)) (ϕ (succ n) r .fst x))
              ∙ cong (fst (ψ n (semiInj r))) (funExt⁻ (cong fst (commϕ n r)) x))

  isChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → ChainComplexMap A B  → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀)
  isChainEquiv f = ((n : Index) (p : _) → isEquiv (chainmap f n p .fst))

  _≃Chain_ : (A : ChainComplex ℓ) (B : ChainComplex ℓ') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ₀)
  A ≃Chain B = Σ[ f ∈ ChainComplexMap A B ] (isChainEquiv f)

  idChainMap : (A : ChainComplex ℓ) → ChainComplexMap A A
  chainmap (idChainMap A) _ _ = idGroupHom
  bdrycomm (idChainMap A) _ _ =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

  invChainMap : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → (A ≃Chain B) → ChainComplexMap B A
  chainmap (invChainMap (record { chainmap = ϕ ; bdrycomm = ϕcomm } , eq)) n p =
    GroupEquiv→GroupHom (invGroupEquiv ((ϕ n p .fst , eq n p) , snd (ϕ n p)))
  bdrycomm (invChainMap {B = B} (record { chainmap = ϕ ; bdrycomm = ϕcomm } , eq)) n p =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ x
        → sym (retEq (_ , eq n (semiInj p)) _)
        ∙∙ cong (invEq (_ , eq n (semiInj p)))
                (sym (funExt⁻ (cong fst (ϕcomm n p)) (invEq (_ , eq (succ n) p) x)))
        ∙∙ cong (invEq (ϕ n (semiInj p) .fst , eq n (semiInj p)) ∘ fst (ChainComplex.bdry B n p))
                (secEq (_ , eq (succ n) p) x))

  invChainEquiv : {A : ChainComplex ℓ} {B : ChainComplex ℓ'}
    → A ≃Chain B → B ≃Chain A
  fst (invChainEquiv e) = invChainMap e
  snd (invChainEquiv e) n p = snd (invEquiv (chainmap (fst e) n p .fst , snd e n p))

  -- TODO: upstream these
  module _ {G H : Group ℓ} (ϕ : GroupHom G H) where
    kerGroup : Group ℓ
    kerGroup = Subgroup→Group G (kerSubgroup ϕ)

    kerGroup≡ : {x y : ⟨ kerGroup ⟩} → x .fst ≡ y .fst → x ≡ y
    kerGroup≡ = Σ≡Prop (isPropIsInKer ϕ)

  open ChainComplex
  open IsGroupHom

  homology : (n : Index⇃) → ChainComplex ℓ → Group ℓ
  homology (n , p) C = ker∂n / img∂+1⊂ker∂n
    where
    Cn+2 = AbGroup→Group (chain C (succ (succ n)) p)
    ∂n = bdry C n (semiInj p)
    ∂n+1 = bdry C (succ n) p
    ker∂n = kerGroup ∂n

    -- Restrict ∂n+1 to ker∂n
    ∂'-fun : Cn+2 .fst → ker∂n .fst
    fst (∂'-fun x) = ∂n+1 .fst x
    snd (∂'-fun x) = t
      where
      opaque
       t : ⟨ fst (kerSubgroup ∂n) (∂n+1 .fst x) ⟩
       t = funExt⁻ (cong fst (bdry²=0 C n p)) x

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
        module C1 = AbGroupStr (chain C (succ n) (semiInj p) .snd)
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
    → (n : Index⇃)
    → GroupHom (homology n C) (homology n D)
  chainComplexMap→HomologyMap {C = C} {D} mp (n , p) = main
    where
    ϕ = chainmap mp
    ϕcomm = bdrycomm mp
    fun : homology (n , p) C .fst → homology (n , p) D .fst
    fun = SQ.elim (λ _ → squash/) f
      λ f g → PT.rec (GroupStr.is-set (homology (n , p) D .snd) _ _ ) (λ r
      →  eq/ _ _ ∣ (fst (ϕ (succ (succ n)) p) (fst r))
                , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n (semiInj (semiInj p)))) _ _)
                         (funExt⁻ (cong fst (ϕcomm (succ n) p)) (fst r)
                       ∙∙ cong (fst (ϕ (succ n) (semiInj p))) (cong fst (snd r))
                       ∙∙ IsGroupHom.pres· (snd (ϕ (succ n) (semiInj p))) _ _
                        ∙ cong₂ (AbGroupStr._+_ (snd (chain D (succ n) (semiInj p))))
                                refl
                                (IsGroupHom.presinv (snd (ϕ (succ n) (semiInj p))) _)) ∣₁)
      where
      f : _ → homology (n , p) D .fst
      f (a , b) = [ (ϕ (succ n) (semiInj p) .fst a)
                , ((λ i → fst (ϕcomm n (semiInj p) i) a)
                ∙∙ cong (fst (ϕ n (semiInj (semiInj p)))) b
                ∙∙ IsGroupHom.pres1 (snd (ϕ n (semiInj (semiInj p))))) ]

    main : GroupHom (homology (n , p) C) (homology (n , p) D)
    fst main = fun
    snd main =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd (homology (n , p) D)) _ _)
          λ a b → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n (semiInj (semiInj p)))) _ _)
              (IsGroupHom.pres· (snd (ϕ (succ n) (semiInj p))) _ _)))

  -- chainComplexMap→HomologyMap : {C D : ChainComplex ℓ}
  --   → (ϕ : ChainComplexMap C D)
  --   → (n : ℕ)
  --   → GroupHom (homology n C) (homology n D)
  -- chainComplexMap→HomologyMap {C = C} {D} ϕ n =
  --   finiteChainComplexMap→HomologyMap n (suc (suc n)) (0 , refl)
  --     (ChainComplexMap→finiteChainComplexMap (suc (suc n)) ϕ)

  chainComplexMap→HomologyMapComp : {C D E : ChainComplex ℓ}
    → (ϕ : ChainComplexMap C D) (ψ : ChainComplexMap D E)
    → (n : Index⇃)
    → chainComplexMap→HomologyMap (compChainMap ϕ ψ) n
     ≡ compGroupHom (chainComplexMap→HomologyMap ϕ n)
                    (chainComplexMap→HomologyMap ψ n)
  chainComplexMap→HomologyMapComp {E = E}
    record { chainmap = ϕ ; bdrycomm = commϕ }
    record { chainmap = ψ ; bdrycomm = commψ } (n , p) =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (n , p) E)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain E n (semiInj (semiInj p)))) _ _) refl)))

  chainComplexMap→HomologyMapId : {C : ChainComplex ℓ} (n : Index⇃)
    → chainComplexMap→HomologyMap (idChainMap C) n ≡ idGroupHom
  chainComplexMap→HomologyMapId {C = C} (n , p) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (n , p) C)) _ _)
          λ _ → cong [_]
            (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n (semiInj (semiInj p)))) _ _) refl)))

  ChainHomotopy→HomologyPath : {A B : ChainComplex ℓ} (f g : ChainComplexMap A B)
    → ChainHomotopy f g
    → (n : Index⇃) → chainComplexMap→HomologyMap f n
                    ≡ chainComplexMap→HomologyMap g n
  ChainHomotopy→HomologyPath {A = A} {B = B} f g ϕ (n , r) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (homology (n , r) _)) _ _)
        λ {(a , p) → eq/ _ _
          ∣ (ChainHomotopy.htpy ϕ (succ n) r .fst a)
          , (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain B n (semiInj (semiInj r))))  _ _)
                    (sym ((funExt⁻ (cong fst (ChainHomotopy.bdryhtpy ϕ n r)) a)
                       ∙ cong₂ _+B_ refl
                                  (cong (fst (ChainHomotopy.htpy ϕ n (semiInj r))) p
                                ∙ IsGroupHom.pres1 (snd (ChainHomotopy.htpy ϕ n (semiInj r))))
                       ∙ AbGroupStr.+IdR (snd (chain B (succ n) (semiInj r))) _))) ∣₁}))
    where
    open GroupTheory (AbGroup→Group (chain B (succ n) (semiInj r)))
    invB = GroupStr.inv (snd (AbGroup→Group (chain B (succ n) (semiInj r))))
    _+B_ = AbGroupStr._+_ (snd (chain B (succ n) (semiInj r)))

  chainComplexEquiv→HomoglogyIso : {C D : ChainComplex ℓ} (f : C ≃Chain D)
    → (n : Index⇃) → GroupIso (homology n C) (homology n D)
  Iso.fun (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    chainComplexMap→HomologyMap f n .fst
  Iso.inv (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    chainComplexMap→HomologyMap (invChainMap (f , eq)) n .fst
  Iso.rightInv (fst (chainComplexEquiv→HomoglogyIso (f , eq) (n , p))) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp
                             (invChainMap (f , eq)) f (n , p)))
           ∙∙  cong (λ f → fst (chainComplexMap→HomologyMap f (n , p)))
                 (ChainComplexMap≡ λ r i
                   →  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (secEq (_ , eq r i))))
           ∙∙ cong fst (chainComplexMap→HomologyMapId (n , p)))

  Iso.leftInv (fst (chainComplexEquiv→HomoglogyIso (f , eq) n)) =
    funExt⁻ (cong fst (sym (chainComplexMap→HomologyMapComp f
                            (invChainMap (f , eq)) n))
          ∙∙ cong (λ f → fst (chainComplexMap→HomologyMap f n))
                  (ChainComplexMap≡
                (λ n i → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
                               (funExt (retEq (_ , eq n i)))))
          ∙∙ cong fst (chainComplexMap→HomologyMapId n))
  snd (chainComplexEquiv→HomoglogyIso (f , eq) n) =
    chainComplexMap→HomologyMap f n .snd

  -- More general version
  homologyIso : (n : Index⇃) (C D : ChainComplex ℓ)
    → (chEq₂ : AbGroupIso (chain C (succ (succ (fst n))) (snd n))
                           (chain D (succ (succ (fst n))) (snd n)))
    → (chEq₁ : AbGroupIso (chain C (succ (fst n)) (semiInj (snd n)))
                           (chain D (succ (fst n)) (semiInj (snd n))))
    → (chEq₀ : AbGroupIso (chain C (fst n) (semiInj (semiInj (snd n))))
                           (chain D (fst n) (semiInj (semiInj (snd n)))))
    → Iso.fun (chEq₀ .fst) ∘ bdry C (fst n) (semiInj (snd n)) .fst
     ≡ bdry D (fst n) (semiInj (snd n)) .fst ∘ Iso.fun (chEq₁ .fst)
    → Iso.fun (chEq₁ .fst) ∘ bdry C (succ (fst n)) (snd n) .fst
     ≡ bdry D (succ (fst n)) (snd n) .fst ∘ Iso.fun (chEq₂ .fst)
    → GroupIso (homology n C) (homology n D)
  homologyIso (n , p) C D chEq₂ chEq₁ chEq₀ eq1 eq2 = main-iso
    where
    F : homology (n , p) C .fst → homology (n , p) D .fst
    F = SQ.elim (λ _ → squash/) f
      λ a b r → eq/ _ _
        (PT.map (λ { (s , t)
          → (Iso.fun (chEq₂ .fst) s)
            , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n (semiInj (semiInj p)))) _ _)
              (sym (funExt⁻ eq2 s)
             ∙ cong (Iso.fun (chEq₁ .fst)) (cong fst t)
             ∙ IsGroupHom.pres· (chEq₁ .snd) _ _
             ∙ cong₂ (snd (chain D (succ n) (semiInj p)) .AbGroupStr._+_)
                     refl
                     (IsGroupHom.presinv (chEq₁ .snd) _))}) r)
      where
      f : _ → homology (n , p) D .fst
      f (a , b) = [ Iso.fun (fst chEq₁) a
                  , sym (funExt⁻ eq1 a) ∙ cong (Iso.fun (chEq₀ .fst)) b
                  ∙ IsGroupHom.pres1 (snd chEq₀) ]

    G : homology (n , p) D .fst → homology (n , p) C .fst
    G = SQ.elim (λ _ → squash/) g
      λ a b r → eq/ _ _
        (PT.map (λ {(s , t)
        → (Iso.inv (chEq₂ .fst) s)
         , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n (semiInj (semiInj p)))) _ _)
             (sym (Iso.leftInv (chEq₁ .fst) _)
            ∙ cong (Iso.inv (chEq₁ .fst)) (funExt⁻ eq2 (Iso.inv (chEq₂ .fst) s))
            ∙ cong (Iso.inv (chEq₁ .fst) ∘ bdry D (succ n) p .fst)
                   (Iso.rightInv (chEq₂ .fst) s)
            ∙ cong (Iso.inv (chEq₁ .fst)) (cong fst t)
            ∙ IsGroupHom.pres· (invGroupIso chEq₁ .snd) _ _
            ∙ cong₂ (snd (chain C (succ n) (semiInj p)) .AbGroupStr._+_)
                     refl
                     ((IsGroupHom.presinv (invGroupIso chEq₁ .snd) _)))}) r)
      where
      g : _ → homology (n , p) C .fst
      g (a , b) = [ Iso.inv (fst chEq₁) a
                  , sym (Iso.leftInv (chEq₀ .fst) _)
                  ∙ cong (Iso.inv (chEq₀ .fst)) (funExt⁻ eq1 (Iso.inv (chEq₁ .fst) a))
                  ∙ cong (Iso.inv (chEq₀ .fst) ∘ bdry D n (semiInj p) .fst)
                         (Iso.rightInv (chEq₁ .fst) a)
                  ∙ cong (Iso.inv (chEq₀ .fst)) b
                  ∙ IsGroupHom.pres1 (invGroupIso chEq₀ .snd) ]

    F-hom : IsGroupHom (homology (n , p) C .snd) F (homology (n , p) D .snd)
    F-hom =
      makeIsGroupHom
        (SQ.elimProp2 (λ _ _ → GroupStr.is-set (homology (n , p) D .snd) _ _)
          λ {(a , s) (b , t)
          → cong [_] (Σ≡Prop (λ _
            → AbGroupStr.is-set (snd (chain D n (semiInj (semiInj p)))) _ _)
                       (IsGroupHom.pres·  (snd chEq₁) _ _)) })

    main-iso : GroupIso (homology (n , p) C) (homology (n , p) D)
    Iso.fun (fst main-iso) = F
    Iso.inv (fst main-iso) = G
    Iso.rightInv (fst main-iso) =
      elimProp (λ _ → GroupStr.is-set (homology (n , p) D .snd) _ _)
        λ{(a , b)
        → cong [_] (Σ≡Prop (λ _
          → AbGroupStr.is-set (snd (chain D n (semiInj (semiInj p)))) _ _)
                    (Iso.rightInv (fst chEq₁) a))}
    Iso.leftInv (fst main-iso) =
      elimProp (λ _ → GroupStr.is-set (homology (n , p) C .snd) _ _)
        λ{(a , b)
        → cong [_] (Σ≡Prop (λ _
          → AbGroupStr.is-set (snd (chain C n (semiInj (semiInj p)))) _ _)
                    (Iso.leftInv (fst chEq₁) a))}
    snd main-iso = F-hom
