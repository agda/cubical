-- Adelman's construction of the free abelian category
-- over an additive category
--   see https://arxiv.org/pdf/2103.08379.pdf
-- Notation is derived from the paper

{-# OPTIONS #-}

module Cubical.Categories.Abelian.Adelman where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Categories.Abelian.Base
open import Cubical.Categories.Additive
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Quotient
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients renaming ([_] to ⟦_⟧)
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' : Level

module _ (A : AdditiveCategory ℓ ℓ') where
  open AdditiveCategory A
  open PreaddCategoryTheory preaddcat

  {-
      Following the paper, we:
        1. Define an additive category A^Δ
        2. Define a congruence relation ~ on A^Δ
        3. Take the quotient  A^Δ / ~  =:  Adel(A)
        4. Define abelian structure on Adel(A)
  -}


  ---------------------------------------
  --  1a. CATEGORY STRUCTURE OF A^Δ
  ---------------------------------------

  -- Objects are composable pairs
  --    r ───ρ───► a ───γ───► c
  record CompPair : Type (ℓ-max ℓ ℓ') where
    constructor cpair
    field
      r : ob
      a : ob
      c : ob
      ρ : Hom[ r , a ]
      γ : Hom[ a , c ]

  open CompPair


  -- Morphisms between composable pairs
  {-  
        X         rX ───ρX───► aX ───γX───► cX
        │         │            │            │
        f         ωf           αf           ψf
        │         │            │            │
        ▼         ▼            ▼            ▼ 
        Y         rY ───ρY───► aY ───γY───► cY
  -}
  record _⇒_ (X Y : CompPair) : Type (ℓ-max ℓ ℓ') where
    constructor cphom
    field
      ω : Hom[ r X , r Y ]
      α : Hom[ a X , a Y ]
      ψ : Hom[ c X , c Y ]
      comm-ρ : ρ X ⋆ α ≡ ω ⋆ ρ Y
      comm-γ : γ X ⋆ ψ ≡ α ⋆ γ Y

  open _⇒_

  -- _⇒_ isomorphic to a Σ-type
  unquoteDecl ⇒IsoΣ = declareRecordIsoΣ ⇒IsoΣ (quote _⇒_)


  -- Identity morphism - each component is identity
  idₐ : {X : CompPair} → X ⇒ X
  idₐ {X} = cphom id id id
      (⋆IdR _ ∙ sym (⋆IdL _)) (⋆IdR _ ∙ sym (⋆IdL _))


  -- Composition - pointwise
  module _ {X Y Z : CompPair}
           (f : X ⇒ Y)
           (g : Y ⇒ Z) where

    _⋆ₐ_ : X ⇒ Z
    _⋆ₐ_ .ω = ω f ⋆ ω g
    _⋆ₐ_ .α = α f ⋆ α g
    _⋆ₐ_ .ψ = ψ f ⋆ ψ g

    _⋆ₐ_ .comm-ρ =
        ρ X ⋆ (α f ⋆ α g)       ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (ρ X ⋆ α f) ⋆ α g       ≡⟨ cong (_⋆ α g) (f .comm-ρ) ⟩
        (ω f ⋆ ρ Y) ⋆ α g       ≡⟨ ⋆Assoc _ _ _ ⟩
        ω f ⋆ (ρ Y ⋆ α g)       ≡⟨ cong (ω f ⋆_) (g .comm-ρ) ⟩
        ω f ⋆ (ω g ⋆ ρ Z)       ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (ω f ⋆ ω g) ⋆ ρ Z       ∎

    _⋆ₐ_ .comm-γ =
        γ X ⋆ (ψ f ⋆ ψ g)       ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (γ X ⋆ ψ f) ⋆ ψ g       ≡⟨ cong (_⋆ ψ g) (f .comm-γ) ⟩
        (α f ⋆ γ Y) ⋆ ψ g       ≡⟨ ⋆Assoc _ _ _ ⟩
        α f ⋆ (γ Y ⋆ ψ g)       ≡⟨ cong (α f ⋆_) (g .comm-γ) ⟩
        α f ⋆ (α g ⋆ γ Z)       ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (α f ⋆ α g) ⋆ γ Z       ∎

    infixr 9 _⋆ₐ_


  -- Equality of `f g : X ⇒ Y` is pointwise
  private
    eqLift : {X Y : CompPair} {f g : X ⇒ Y}
          → (ω f ≡ ω g) → (α f ≡ α g) → (ψ f ≡ ψ g)
          → f ≡ g
    eqLift eqω eqα eqψ = isoFunInjective ⇒IsoΣ _ _
        (ΣPathP (eqω , ΣPathP (eqα , ΣPathP (eqψ , ΣPathP
        (toPathP (isSetHom _ _ _ _) , toPathP (isSetHom _ _ _ _))))))


  -- Left identity
  ⋆ₐIdL : {X Y : CompPair} (f : X ⇒ Y) →
      idₐ ⋆ₐ f ≡ f
  ⋆ₐIdL f = eqLift (⋆IdL _) (⋆IdL _) (⋆IdL _)

  -- Right identity
  ⋆ₐIdR : {X Y : CompPair} (f : X ⇒ Y) →
      f ⋆ₐ idₐ ≡ f
  ⋆ₐIdR f = eqLift (⋆IdR _) (⋆IdR _) (⋆IdR _)

  -- Associativity
  ⋆ₐAssoc : {X Y Z W : CompPair}
    (f : X ⇒ Y) (g : Y ⇒ Z) (h : Z ⇒ W) →
      (f ⋆ₐ g) ⋆ₐ h  ≡  f ⋆ₐ (g ⋆ₐ h)
  ⋆ₐAssoc f g h = eqLift (⋆Assoc _ _ _) (⋆Assoc _ _ _) (⋆Assoc _ _ _)

  -- `⇒` is a set
  isSet⇒ : ∀ {X Y} → isSet (X ⇒ Y)
  isSet⇒ = isOfHLevelRetractFromIso 2 ⇒IsoΣ
    (isSetΣ isSetHom λ ω →   isSetΣ isSetHom λ α →   isSetΣ isSetHom λ ψ →
          isProp→isSet (isPropΣ (isSetHom _ _) (λ comm-ρ → isSetHom _ _)))


  A^Δ : Category (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  A^Δ .Category.ob = CompPair
  A^Δ .Category.Hom[_,_] = _⇒_
  A^Δ .Category.id = idₐ
  A^Δ .Category._⋆_ = _⋆ₐ_
  A^Δ .Category.⋆IdL = ⋆ₐIdL
  A^Δ .Category.⋆IdR = ⋆ₐIdR
  A^Δ .Category.⋆Assoc = ⋆ₐAssoc
  A^Δ .Category.isSetHom = isSet⇒


  ---------------------------------------
  --  1b. PREADDITIVE STRUCTURE ON A^Δ
  ---------------------------------------

  -- Abelian group structure
  module _ {X Y : CompPair} where
  
    0ₐ : X ⇒ Y
    0ₐ = cphom 0h 0h 0h ((⋆0hr _) ∙ (sym (⋆0hl _)))
                        ((⋆0hr _) ∙ (sym (⋆0hl _)))

    _+ₐ_ : (f g : X ⇒ Y) → (X ⇒ Y)
    f +ₐ g = cphom (ω f + ω g) (α f + α g) (ψ f + ψ g)
      (
        ρ X ⋆ (α f + α g)           ≡⟨ ⋆distl+ _ _ _ ⟩
        ρ X ⋆ α f  +  ρ X ⋆ α g     ≡⟨ cong₂ _+_ (comm-ρ f) (comm-ρ g) ⟩
        ω f ⋆ ρ Y  +  ω g ⋆ ρ Y     ≡⟨ sym (⋆distr+ _ _ _) ⟩
        (ω f + ω g) ⋆ ρ Y           ∎
      )(
        γ X ⋆ (ψ f + ψ g)           ≡⟨ ⋆distl+ _ _ _ ⟩
        γ X ⋆ ψ f  +  γ X ⋆ ψ g     ≡⟨ cong₂ _+_ (comm-γ f) (comm-γ g) ⟩
        α f ⋆ γ Y  +  α g ⋆ γ Y     ≡⟨ sym (⋆distr+ _ _ _) ⟩
        (α f + α g) ⋆ γ Y           ∎
      )

    infixr 7 _+ₐ_

    -ₐ : X ⇒ Y → X ⇒ Y
    -ₐ f = cphom (- ω f) (- α f) (- ψ f)
      (
        ρ X ⋆ (- α f)     ≡⟨ -distr⋆ _ _ ⟩
        - ρ X ⋆ α f       ≡⟨ cong -_ (comm-ρ f) ⟩
        - ω f ⋆ ρ Y       ≡⟨ sym (-distl⋆ _ _) ⟩
        (- ω f) ⋆ ρ Y     ∎
      )(
        γ X ⋆ (- ψ f)     ≡⟨ -distr⋆ _ _ ⟩
        - γ X ⋆ ψ f       ≡⟨ cong -_ (comm-γ f) ⟩
        - α f ⋆ γ Y       ≡⟨ sym (-distl⋆ _ _) ⟩
        (- α f) ⋆ γ Y     ∎
      )


    -- Abelian group axioms
    +ₐassoc : (f g h : X ⇒ Y) →
      f +ₐ (g +ₐ h) ≡ (f +ₐ g) +ₐ h
    +ₐassoc f g h = eqLift (+assoc _ _ _) (+assoc _ _ _) (+assoc _ _ _)

    +ₐidr : (f : X ⇒ Y) → f +ₐ 0ₐ ≡ f
    +ₐidr f = eqLift (+idr _) (+idr _) (+idr _)

    +ₐinvr : (f : X ⇒ Y) → f +ₐ (-ₐ f) ≡ 0ₐ
    +ₐinvr f = eqLift (+invr _) (+invr _) (+invr _)

    +ₐcomm : (f g : X ⇒ Y) → f +ₐ g ≡ g +ₐ f
    +ₐcomm f g = eqLift (+comm _ _) (+comm _ _) (+comm _ _)


  -- habstrₐ : HomAbStr A^Δ
  -- habstrₐ = homabstr (λ _ _ →
  --     abgroupstr (0ₐ) (_+ₐ_) (-ₐ)
  --     (makeIsAbGroup  isSet⇒  +ₐassoc  +ₐidr  +ₐinvr  +ₐcomm))


  -- Distributivity
  module _ {X Y Z : CompPair} where

    ⋆distl+ₐ : (f : X ⇒ Y) (g g' : Y ⇒ Z) →
        f ⋆ₐ (g +ₐ g')  ≡  (f ⋆ₐ g) +ₐ (f ⋆ₐ g')
    ⋆distl+ₐ f g g' = eqLift (⋆distl+ _ _ _) (⋆distl+ _ _ _) (⋆distl+ _ _ _)

    ⋆distr+ₐ : (f f' : X ⇒ Y) (g : Y ⇒ Z) →
        (f +ₐ f') ⋆ₐ g  ≡  (f ⋆ₐ g) +ₐ (f' ⋆ₐ g)
    ⋆distr+ₐ f g g' = eqLift (⋆distr+ _ _ _) (⋆distr+ _ _ _) (⋆distr+ _ _ _)


  A^Δ-preadd : PreaddCategory (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  A^Δ-preadd .PreaddCategory.cat = A^Δ
  A^Δ-preadd .PreaddCategory.preadd .PreaddCategoryStr.homAbStr X Y =
    abgroupstr (0ₐ) (_+ₐ_) (-ₐ)
      (makeIsAbGroup  isSet⇒  +ₐassoc  +ₐidr  +ₐinvr  +ₐcomm)
  A^Δ-preadd .PreaddCategory.preadd .PreaddCategoryStr.⋆distl+ = ⋆distl+ₐ
  A^Δ-preadd .PreaddCategory.preadd .PreaddCategoryStr.⋆distr+ = ⋆distr+ₐ
  

  ---------------------------------------
  --  1c. ADDITIVE STRUCTURE ON A^Δ
  ---------------------------------------

  -- Zero object
  private
    open ZeroObject zero renaming (z to zA)

    zA→ : {x : ob} → Hom[ zA , x ]
    zA→ {x} = zInit x .fst

    →zA : {x : ob} → Hom[ x , zA ]
    →zA {x} = zTerm x .fst

  zₐ : CompPair
  zₐ = cpair zA zA zA id id

  zₐInit : isInitial A^Δ zₐ
  zₐInit X = (cphom zA→ zA→ zA→ (isContr→isProp (zInit _) _ _)
      (isContr→isProp (zInit _) _ _)) ,
      λ f → eqLift (zInit _ .snd _) (zInit _ .snd _) (zInit _ .snd _)

  zₐTerm : isTerminal A^Δ zₐ
  zₐTerm X = (cphom →zA →zA →zA (isContr→isProp (zTerm _) _ _)
      (isContr→isProp (zTerm _) _ _)) ,
      λ f → eqLift (zTerm _ .snd _) (zTerm _ .snd _) (zTerm _ .snd _)

  
  -- Biproducts
  open MatrixNotation A

  module _ (X Y : CompPair) where
    biprodₐ : Biproduct A^Δ-preadd X Y
    biprodₐ .Biproduct.x⊕y =
      cpair (r X ⊕ r Y) (a X ⊕ a Y) (c X ⊕ c Y)
            (ρ X ` 0h ∣ 0h ` ρ Y) (γ X ` 0h ∣ 0h ` γ Y)

    -- Everything else follows pointwise
    biprodₐ .Biproduct.i₁ = cphom i₁ i₁ i₁ (sym (i₁⋆diag _ _)) (sym (i₁⋆diag _ _))
    biprodₐ .Biproduct.i₂ = cphom i₂ i₂ i₂ (sym (i₂⋆diag _ _)) (sym (i₂⋆diag _ _))
    biprodₐ .Biproduct.π₁ = cphom π₁ π₁ π₁      (diag⋆π₁ _ _)       (diag⋆π₁ _ _)
    biprodₐ .Biproduct.π₂ = cphom π₂ π₂ π₂      (diag⋆π₂ _ _)       (diag⋆π₂ _ _)

    biprodₐ .Biproduct.isBipr .IsBiproduct.i₁⋆π₁ = eqLift i₁⋆π₁ i₁⋆π₁ i₁⋆π₁
    biprodₐ .Biproduct.isBipr .IsBiproduct.i₁⋆π₂ = eqLift i₁⋆π₂ i₁⋆π₂ i₁⋆π₂
    biprodₐ .Biproduct.isBipr .IsBiproduct.i₂⋆π₁ = eqLift i₂⋆π₁ i₂⋆π₁ i₂⋆π₁
    biprodₐ .Biproduct.isBipr .IsBiproduct.i₂⋆π₂ = eqLift i₂⋆π₂ i₂⋆π₂ i₂⋆π₂
    biprodₐ .Biproduct.isBipr .IsBiproduct.∑π⋆i  = eqLift ∑π⋆i  ∑π⋆i  ∑π⋆i


  ---------------------------------------
  --  2. CONGRUENCE RELATION ~ ON A^Δ
  ---------------------------------------
  
  {-  Given two parallel morphisms

          X           rX ───ρX───► aX ───γX───► cX
          ││          ││           ││           ││
         f││g       ωf││ωg       αf││αg       ψf││ψg
          ││          ││           ││           ││
          ▼▼          ▼▼           ▼▼           ▼▼ 
          Y           rY ───ρY───► aY ───γY───► cY

      we say f ~ g if there exist

               ╭────────── aX ───γX───► cX
               │           ││            │
             ∃ σ₁        αf││αg        ∃ σ₂
               │           ││            │
               ▼           ▼▼            │
              rY ───ρY───► aY ◄──────────╯

      such that  αf ─ αg  ≡  σ₁ ⋆ ρY  +  γX ⋆ σ₂.
  -}
  record _~_ {X Y : CompPair} (f g : X ⇒ Y) : Type (ℓ-max ℓ ℓ') where
    field
      σ₁ : Hom[ a X , r Y ]
      σ₂ : Hom[ c X , a Y ]
      eq :  α f ─ α g  ≡  σ₁ ⋆ ρ Y  +  γ X ⋆ σ₂

  infix 5 _~_
  open _~_


  -- Reflexivity
  ~refl : {X Y : CompPair} (f : X ⇒ Y) → f ~ f
  ~refl f .σ₁ = 0h
  ~refl f .σ₂ = 0h
  ~refl {X} {Y} f .eq =
      α f ─ α f                   ≡⟨ +invr _ ⟩
      0h                          ≡⟨ sym (+idr _) ⟩
      0h + 0h                     ≡⟨ cong (_+ 0h) (sym (⋆0hl _)) ⟩
      (0h ⋆ ρ Y) + 0h             ≡⟨ cong ((0h ⋆ ρ Y) +_) (sym (⋆0hr _)) ⟩
      (0h ⋆ ρ Y) + (γ X ⋆ 0h)     ∎


  module _ {X Y : CompPair} where
    -- Congruent with addition
    ~cong+ : (f f' g g' : X ⇒ Y) →
        f ~ f' → g ~ g' → (f +ₐ g) ~ (f' +ₐ g')
    ~cong+ f f' g g' f~f' g~g' = λ where
      .σ₁ →  σ₁ f~f' + σ₁ g~g'
      .σ₂ →  σ₂ f~f' + σ₂ g~g'
      .eq → 
        (α f + α g) ─ (α f' + α g')
                ≡⟨ cong ((α f + α g) +_) (-dist+ _ _) ⟩
        (α f + α g) + (- α f' ─ α g')
                ≡⟨ +4comm _ _ _ _ ⟩
        (α f ─ α f') + (α g ─ α g')
                ≡⟨ cong₂ _+_ (f~f' .eq) (g~g' .eq) ⟩
        (σ₁ f~f' ⋆ ρ Y  +  γ X ⋆ σ₂ f~f')  +  (σ₁ g~g' ⋆ ρ Y  +  γ X ⋆ σ₂ g~g')
                ≡⟨ +4comm _ _ _ _ ⟩
        (σ₁ f~f' ⋆ ρ Y  +  σ₁ g~g' ⋆ ρ Y)  +  (γ X ⋆ σ₂ f~f'  +  γ X ⋆ σ₂ g~g')
                ≡⟨ sym (cong₂ _+_ (⋆distr+ _ _ _) (⋆distl+ _ _ _)) ⟩
        (σ₁ f~f' + σ₁ g~g') ⋆ ρ Y  +  γ X ⋆ (σ₂ f~f' + σ₂ g~g')
                ∎

    -- Congruent with negation
    ~cong- : (f g : X ⇒ Y) →
        f ~ g → (-ₐ f) ~ (-ₐ g)
    ~cong- f g f~g = λ where
      .σ₁ →  - σ₁ f~g
      .σ₂ →  - σ₂ f~g
      .eq →
        - α f ─ (- α g)                           ≡⟨ sym (-dist+ _ _) ⟩
        - (α f ─ α g)                             ≡⟨ cong -_ (f~g .eq) ⟩
        - (σ₁ f~g ⋆ ρ Y  +  γ X ⋆ σ₂ f~g)         ≡⟨ -dist+ _ _ ⟩
        - (σ₁ f~g ⋆ ρ Y)  +  - (γ X ⋆ σ₂ f~g)     ≡⟨ cong (_─ _ ⋆ _) (sym (-distl⋆ _ _)) ⟩
        (- σ₁ f~g) ⋆ ρ Y  +  - (γ X ⋆ σ₂ f~g)     ≡⟨ cong (_ ⋆ _ +_) (sym (-distr⋆ _ _)) ⟩
        (- σ₁ f~g) ⋆ ρ Y  +  γ X ⋆ (- σ₂ f~g)     ∎


  -- Congruent with composition
  ~cong⋆ : {X Y Z : CompPair}
          (f f' : X ⇒ Y) → f ~ f' →
          (g g' : Y ⇒ Z) → g ~ g'
        → (f ⋆ₐ g) ~ (f' ⋆ₐ g')

  ~cong⋆ {X} {Y} {Z} f f' f~f' g g' g~g' = λ where
    .σ₁ → (σ₁ f~f') ⋆ ω g  +  α f' ⋆ (σ₁ g~g')
    .σ₂ → (σ₂ f~f') ⋆ α g  +  ψ f' ⋆ (σ₂ g~g')
    .eq →
      let σ₁f⋆ωg⋆ρZ   = (σ₁ f~f' ⋆ ω g) ⋆ ρ Z;    γX⋆σ₂f⋆αg  = γ X ⋆ (σ₂ f~f' ⋆ α g);
           αf'⋆σ₁g⋆ρZ = (α f' ⋆ σ₁ g~g') ⋆ ρ Z;   γX⋆ψf'⋆σ₂g = γ X ⋆ (ψ f' ⋆ σ₂ g~g') in
      α f ⋆ α g  ─  α f' ⋆ α g'
              ≡⟨ cong (_ +_) (sym (+idl _)) ⟩
      α f ⋆ α g  +  0h  ─  α f' ⋆ α g'
              ≡⟨ cong (λ u → _ + u ─ _) (sym (+invl _)) ⟩
      α f ⋆ α g  +  (- α f' ⋆ α g  +  α f' ⋆ α g)  ─  α f' ⋆ α g'
              ≡⟨ sym (+4assoc _ _ _ _) ⟩
      (α f ⋆ α g  ─  α f' ⋆ α g)  +  (α f' ⋆ α g  ─  α f' ⋆ α g')
              ≡⟨ cong₂ _+_ eq1 eq2 ⟩
      (σ₁f⋆ωg⋆ρZ  +  γX⋆σ₂f⋆αg)  +  (αf'⋆σ₁g⋆ρZ  +  γX⋆ψf'⋆σ₂g)
              ≡⟨ +4comm _ _ _ _ ⟩
      (σ₁f⋆ωg⋆ρZ  +  αf'⋆σ₁g⋆ρZ)  +  (γX⋆σ₂f⋆αg  +  γX⋆ψf'⋆σ₂g)
              ≡⟨ cong₂ _+_ (sym (⋆distr+ _ _ _)) (sym (⋆distl+ _ _ _)) ⟩
      (σ₁ f~f' ⋆ ω g + α f' ⋆ σ₁ g~g') ⋆ ρ Z + γ X ⋆ (σ₂ f~f' ⋆ α g + ψ f' ⋆ σ₂ g~g')
              ∎
      where
          eq1 =
            α f ⋆ α g  ─  α f' ⋆ α g
                    ≡⟨ cong (α f ⋆ α g +_) (sym (-distl⋆ _ _)) ⟩
            α f ⋆ α g  +  (- α f') ⋆ α g
                    ≡⟨ sym (⋆distr+ _ _ _) ⟩
            (α f ─ α f') ⋆ α g
                    ≡⟨ cong (_⋆ α g) (eq f~f') ⟩
            (σ₁ f~f' ⋆ ρ Y  +  γ X ⋆ σ₂ f~f') ⋆ α g
                    ≡⟨ ⋆distr+ _ _ _ ⟩
            (σ₁ f~f' ⋆ ρ Y) ⋆ α g  +  (γ X ⋆ σ₂ f~f') ⋆ α g
                    ≡⟨ cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _) ⟩
            σ₁ f~f' ⋆ (ρ Y ⋆ α g)  +  γ X ⋆ (σ₂ f~f' ⋆ α g)
                    ≡⟨ cong (λ u → _ ⋆ u + _ ⋆ (σ₂ f~f' ⋆ _)) (g .comm-ρ) ⟩
            σ₁ f~f' ⋆ (ω g ⋆ ρ Z)  +  γ X ⋆ (σ₂ f~f' ⋆ α g)
                    ≡⟨ cong (_+ _ ⋆ (σ₂ f~f' ⋆ _)) (sym (⋆Assoc _ _ _)) ⟩
            (σ₁ f~f' ⋆ ω g) ⋆ ρ Z  +  γ X ⋆ (σ₂ f~f' ⋆ α g)
                    ∎
          eq2 =
            α f' ⋆ α g  ─  α f' ⋆ α g'
                    ≡⟨ cong (_ +_) (sym (-distr⋆ _ _)) ⟩
            α f' ⋆ α g  +  α f' ⋆ (- α g')
                    ≡⟨ sym (⋆distl+ _ _ _) ⟩
            α f' ⋆ (α g  ─  α g')
                    ≡⟨ cong (_ ⋆_) (eq g~g') ⟩
            α f' ⋆ (σ₁ g~g' ⋆ ρ Z  +  γ Y ⋆ σ₂ g~g')
                    ≡⟨ ⋆distl+ _ _ _ ⟩
            α f' ⋆ (σ₁ g~g' ⋆ ρ Z)  +  α f' ⋆ (γ Y ⋆ σ₂ g~g')
                    ≡⟨ cong₂ _+_ (sym (⋆Assoc _ _ _)) (sym (⋆Assoc _ _ _)) ⟩
            (α f' ⋆ σ₁ g~g') ⋆ ρ Z  +  (α f' ⋆ γ Y) ⋆ σ₂ g~g'
                    ≡⟨ cong (λ u → (_ ⋆ σ₁ g~g') ⋆ _ + u ⋆ _) (sym (f' .comm-γ)) ⟩
            (α f' ⋆ σ₁ g~g') ⋆ ρ Z  +  (γ X ⋆ ψ f') ⋆ σ₂ g~g'
                    ≡⟨ cong (((α f' ⋆ σ₁ g~g') ⋆ ρ Z) +_) (⋆Assoc _ _ _) ⟩
            (α f' ⋆ σ₁ g~g') ⋆ ρ Z  +  γ X ⋆ (ψ f' ⋆ σ₂ g~g')
                    ∎


  ---------------------------------------
  --  3.  Adel(A)  :=  A^Δ / ~
  ---------------------------------------

  AdelAddCat : AdditiveCategory (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  AdelAddCat = AdditiveQuotient
    record {
      preaddcat = A^Δ-preadd;
      addit = record {
        zero = record { z = zₐ ; zInit = zₐInit ; zTerm = zₐTerm };
        biprod = biprodₐ } }
    _~_ ~refl ~cong⋆ ~cong+ ~cong-


  ---------------------------------------
  --  4. ABELIAN STRUCTURE ON Adel(A)
  ---------------------------------------

  private
    A^Δ/~      = AdelAddCat .AdditiveCategory.preaddcat
    Hom[_,_]/~ = AdelAddCat .AdditiveCategory.Hom[_,_]
  
  module _ {X Y : CompPair} (f : X ⇒ Y) where

    AdelKerObj = cpair (r X ⊕ r Y) (a X ⊕ r Y) (c X ⊕ a Y)
          (ρ X ` 0h ∣ 0h ` id) (γ X ` 0h ∣ α f ` ρ Y)

    AdelKer : AdelKerObj ⇒ X
    AdelKer = cphom (id ` 0h) (id ` 0h) (id ` 0h) {!   !} {!   !}

    ker⋆f : AdelKer ⋆ₐ f ~ 0ₐ
    ker⋆f = record {
      σ₁ = (0h ` - id);
      σ₂ = (0h ` id);
      eq =
          (id ` 0h) ⋆ α f  ─  0h
                  ≡⟨ {!   !} ⟩
          (id ` 0h) ⋆ α f
                  ≡⟨ {!   !} ⟩
          (π₁ ⋆ id  +  π₂ ⋆ 0h) ⋆ α f
                  ≡⟨ {!   !} ⟩
          (π₁  +  0h) ⋆ α f
                  ≡⟨ {!   !} ⟩
          π₁ ⋆ α f
                  ≡⟨ {!   !} ⟩
          (0h ` - id) ⋆ ρ Y  +  (γ X ` 0h ∣ α f ` ρ Y) ⋆ (0h ` id)
                  ∎
      }


    module _ (W : CompPair) (t : W ⇒ X) (t⋆f~0 : t ⋆ₐ f ~ 0ₐ) where

      u : W ⇒ AdelKerObj
      u = cphom (ω t ∣ - ρ W ⋆ (σ₁ t⋆f~0))
                (α t ∣ - σ₁ t⋆f~0)
                (ψ t ∣ σ₂ t⋆f~0)
                {!   !} {!   !}

      u-comm : u ⋆ₐ AdelKer ~ t
      u-comm = record {
        σ₁ = 0h ;
        σ₂ = 0h ;
        eq =
          α u ⋆ α AdelKer  ─  α t
                  ≡⟨ refl ⟩
          (α t ∣ - σ₁ t⋆f~0) ⋆ (id ` 0h)  ─  α t
                  ≡⟨ cong (_─ _) (innerProd _ _ _ _) ⟩
          (α t ⋆ id  +  (- σ₁ t⋆f~0) ⋆ 0h)  ─  α t
                  ≡⟨ cong₂ (λ u₁ v → (u₁ + v) ─ _) (⋆IdR _) (⋆0hr _) ⟩
          (α t  +  0h)  ─  α t
                  ≡⟨ cong (_─ _) (+idr _) ⟩
          α t  ─  α t
                  ≡⟨ +invr _ ⟩
          0h
                  ≡⟨ sym (+idr _) ⟩
          0h  +  0h
                  ≡⟨ sym (cong₂ _+_ (⋆0hl _) (⋆0hr _)) ⟩
          0h ⋆ ρ X  +  γ W ⋆ 0h
                  ∎
        }


      u-unq : (v : W ⇒ AdelKerObj) → (v ⋆ₐ AdelKer ~ t) → v ~ u
      u-unq v v⋆k~t = record {
        σ₁ = (σ₁₁ ∣ σ₁₂);
        σ₂ = (σ₂₁ ∣ σ₂₂);
        eq =
          α v ─ (α t ∣ - σ₁ t⋆f~0)
                  ≡⟨ {!   !} ⟩
          (α v ⋆ π₁ ∣ α v ⋆ π₂) ─ (α t ∣ - σ₁ t⋆f~0)
                  ≡⟨ {!   !} ⟩
          (α v ⋆ π₁ ─ α t  ∣  α v ⋆ π₂ + σ₁ t⋆f~0)
                  ≡⟨ {!   !} ⟩
          (σ₁₁ ⋆ ρ X  +  γ W ⋆ σ₂₁  ∣   σ₁₂  +  γ W ⋆ σ₂₂)
                  ≡⟨ {!   !} ⟩
          (σ₁₁ ⋆ ρ X  ∣  σ₁₁ ⋆ 0h)  +  (σ₁₂ ⋆ 0h  ∣  σ₁₂ ⋆ id)  +  (γ W ⋆ σ₂₁  ∣  γ W ⋆ σ₂₂)
                  ≡⟨ {!   !} ⟩
          (σ₁₁ ⋆ (ρ X ∣ 0h)  +  σ₁₂ ⋆ (0h ∣ id))  +  (γ W ⋆ σ₂₁  ∣  γ W ⋆ σ₂₂)
                  ≡⟨ {!   !} ⟩
          (σ₁₁ ∣ σ₁₂) ⋆ ((ρ X ∣ 0h) ` (0h ∣ id))  +  (γ W ⋆ σ₂₁  ∣  γ W ⋆ σ₂₂)
                  ≡⟨ {!   !} ⟩
          (σ₁₁ ∣ σ₁₂) ⋆ (ρ X ` 0h ∣ 0h ` id)  +  γ W ⋆ (σ₂₁ ∣ σ₂₂)
                  ∎
        }
        where
          σ₁₁ : Hom[ a W , r X ]
          σ₁₁ = σ₁ v⋆k~t

          σ₁₂ : Hom[ a W , r Y ]
          σ₁₂ = {!   !}

          σ₂₁ : Hom[ c W , a X ]
          σ₂₁ = σ₂ v⋆k~t

          σ₂₂ : Hom[ c W , r Y ]
          σ₂₂ = {!   !}

          eq1 :  α v ⋆ π₁ ─ α t  ≡  σ₁₁ ⋆ ρ X  +  γ W ⋆ σ₂₁
          eq1 = {!  v⋆k~t .eq  !}

          eq2 :  α v ⋆ π₂ + σ₁ t⋆f~0  ≡  σ₁₂  +  γ W ⋆ σ₂₂
          eq2 = {!  t⋆f~0 .eq !}

      -- v⋆k~t : v ⋆ₐ AdelKer ~ t
      --    σ₁ : Hom[ a W , r X ]
      --    σ₂ : Hom[ c W , a X ]
      --    eq :  α v ⋆ (id ` 0h)  ─  α t  ≡  σ₁ v⋆k~t ⋆ ρ X  +  γ W ⋆ σ₂ v⋆k~t
      --          α v ⋆ π₁  ─  α t  ≡  σ₁ v⋆k~t ⋆ ρ X  +  γ W ⋆ σ₂ v⋆k~t

      -- t⋆f~0 : t ⋆ₐ f ~ 0ₐ
      --    σ₁ : Hom[ a W , r Y ]
      --    σ₂ : Hom[ c W , a Y ]
      --    eq :  α t ⋆ α f  ─  α 0ₐ  ≡  σ₁ t⋆f~0 ⋆ ρ Y  +  γ W ⋆ σ₂ t⋆f~0
      --          α t ⋆ α f  ≡  σ₁ t⋆f~0 ⋆ ρ Y  +  γ W ⋆ σ₂ t⋆f~0


    -- univKer : ∀ (W : CompPair) (t : W ⇒ X)
    --       → (t ⋆ₐ f) ~ 0ₐ →
    --       ∃![ u ∈ (W ⇒ AdelKerObj) ] ((u ⋆ₐ AdelKer) ~ t)
    -- univKer W t t⋆f~0 = ({!   !} ,
    --                      {!   !}) ,
    --                      {!   !}



  module _ {X Y : CompPair} (⟦f⟧ : Hom[ X , Y ]/~) where

    -- Now define kernel on quotient
    AdelKer/~ : Kernel A^Δ/~ ⟦f⟧
    AdelKer/~ = record {
      k = rec {!   !} AdelKerObj {!   !} ⟦f⟧ ;
      ker = ⟦ rec {!   !} {! AdelKer !} {!   !} ⟦f⟧ ⟧ ;
      isKer = {!   !} }
    
    -- record {
    --   k = cpair (r X ⊕ r Y) (a X ⊕ r Y) (c X ⊕ a Y)
    --         ( ρ X ` 0h ∣ 0h ` id ) (γ X ` {!   !} ∣ {!  α ⟦f⟧ !} ` {!   !}) ;
    --   ker = {!   !} ;
    --   isKer = {!   !} }

    -- Cokernels
    -- AdelCoker : (⟦f⟧ : Hom[ X , Y ]/~) → Cokernel A^Δ/~ ⟦f⟧
    -- AdelCoker = {!   !}


  Adel : AbelianCategory (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  Adel = {!   !}
