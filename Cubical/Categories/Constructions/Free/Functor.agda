-- Free functor between categories generated from two graphs and a
-- function on nodes between them
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Constructions.Free.Functor where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Empty
open import Cubical.Data.Equality.Conversion
open import Cubical.Data.Equality hiding (id; sym)
  renaming (_≡_ to Eq; refl to reflEq; _∙_ to _∙Eq_; transport to transportEq)
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Free.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.UnderlyingGraph

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso

module FreeFunctor (G : Graph ℓg ℓg')
                   (H : Graph ℓh ℓh')
                   (ϕ : G .Node → H .Node) where
  module FreeCatG = FreeCategory G
  open FreeCatG.Exp
  FG = FreeCatG.FreeCat
  Exp = FreeCatG.Exp
  data FExp : H .Node → H .Node
            → Type (((ℓ-max ℓg (ℓ-max ℓg' (ℓ-max ℓh ℓh'))))) where
    -- free category on H with a functor from G to H freely added
    ↑_ : ∀ {A B} → H .Edge A B → FExp A B
    idₑ : ∀ {A} → FExp A A
    _⋆ₑ_ : ∀ {A B C} → FExp A B → FExp B C → FExp A C
    F⟪_⟫ : ∀ {A B} → Exp A B → FExp (ϕ A) (ϕ B)

    ⋆ₑIdL : ∀ {A B} (e : FExp A B) → idₑ ⋆ₑ e ≡ e
    ⋆ₑIdR : ∀ {A B} (e : FExp A B) → e ⋆ₑ idₑ ≡ e
    ⋆ₑAssoc : ∀ {A B C D} (e : FExp A B)(f : FExp B C)(g : FExp C D)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    F-idₑ : ∀ {A} → F⟪ idₑ {A = A} ⟫ ≡ idₑ
    F-seqₑ : ∀ {A B C} (f : Exp A B)(g : Exp B C)
           → F⟪ f ⋆ₑ g ⟫ ≡ (F⟪ f ⟫ ⋆ₑ F⟪ g ⟫)

    isSetFExp : ∀ {A B} → isSet (FExp A B)

  FH : Category _ _
  FH .ob = H .Node
  FH .Hom[_,_] = FExp
  FH .id = idₑ
  FH ._⋆_ = _⋆ₑ_
  FH .⋆IdL = ⋆ₑIdL
  FH .⋆IdR = ⋆ₑIdR
  FH .⋆Assoc = ⋆ₑAssoc
  FH .isSetHom = isSetFExp

  Fϕ : Functor FG FH
  Fϕ .F-ob = ϕ
  Fϕ .F-hom = F⟪_⟫
  Fϕ .F-id = F-idₑ
  Fϕ .F-seq = F-seqₑ

  -- The universal interpretation
  ηG = FreeCatG.η

  ηH : Interp H FH
  ηH $g x = x
  ηH <$g> x = ↑ x

  Fϕ-homo : GraphHom G (Cat→Graph FH)
  Fϕ-homo $g x = ϕ x
  Fϕ-homo <$g> x = F⟪ ↑ x ⟫

  ηϕ : Eq (Fϕ .F-ob ∘f ηG ._$g_) (ηH ._$g_ ∘f ϕ)
  ηϕ = reflEq

  module _ {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'} {𝓕 : Functor 𝓒 𝓓} where
    {-

       It is very important for the implementation of the functor
       solver that ıϕ uses Data.Equality.Eq rather than Path. The
       reason is that the case semH-hom (F⟪_⟫ {A}{B} x) inherently
       involves a transport when expressed at this level of
       generality, and transport of a refl is the identity function
       for Eq but not for Path.

    -}
    module Semantics (ıG : Interp G 𝓒) (ıH : Interp H 𝓓)
                     (ıϕ : Eq (𝓕 .F-ob ∘f ıG ._$g_) (ıH ._$g_ ∘f ϕ))
           where
      semG = FreeCatG.Semantics.sem 𝓒 ıG

      semH-hom : ∀ {A B} → FExp A B → 𝓓 [ ıH $g A , ıH $g B ]
      semH-hom (↑ x) = ıH <$g> x
      semH-hom idₑ = 𝓓 .id
      semH-hom (e ⋆ₑ e₁) = semH-hom e ⋆⟨ 𝓓 ⟩ semH-hom e₁
      semH-hom (F⟪_⟫ {A}{B} x) =
        transportEq (λ (f : G .Node → 𝓓 .ob) → 𝓓 [ f A , f B ])
                    ıϕ
                    (𝓕 ⟪ semG ⟪ x ⟫ ⟫)
      semH-hom (⋆ₑIdL f i) = 𝓓 .⋆IdL (semH-hom f) i
      semH-hom (⋆ₑIdR f i) = 𝓓 .⋆IdR (semH-hom f) i
      semH-hom (⋆ₑAssoc f f' f'' i) =
        𝓓 .⋆Assoc (semH-hom f) (semH-hom f') (semH-hom f'') i
      semH-hom (F-idₑ {A} i) = unbound i
        where
          unbound : transportEq (λ f → 𝓓 [ f A , f A ]) ıϕ (𝓕 ⟪ semG ⟪ idₑ ⟫ ⟫)
                    ≡ 𝓓 .id
          unbound =
            J (λ g p → transportEq (λ f → 𝓓 [ f A , f A ]) p
                                   (𝓕 ⟪ semG ⟪ idₑ ⟫ ⟫)
                       ≡ 𝓓 .id)
              ((𝓕 ∘F semG) .F-id) ıϕ
      semH-hom (F-seqₑ {A}{B}{C} e e' i) = unbound i
        where
          unbound :
            transportEq (λ f → 𝓓 [ f A , f C ]) ıϕ (𝓕 ⟪ semG ⟪ e ⋆ₑ e' ⟫ ⟫)
            ≡ (transportEq (λ f → 𝓓 [ f A , f B ]) ıϕ (𝓕 ⟪ semG ⟪ e ⟫ ⟫))
              ⋆⟨ 𝓓 ⟩ (transportEq (λ f → 𝓓 [ f B , f C ]) ıϕ
                                  (𝓕 ⟪ semG ⟪ e' ⟫ ⟫))
          unbound =
            J (λ g p →
                transportEq (λ f → 𝓓 [ f A , f C ]) p (𝓕 ⟪ semG ⟪ e ⋆ₑ e' ⟫ ⟫)
                ≡ (transportEq (λ f → 𝓓 [ f A , f B ]) p (𝓕 ⟪ semG ⟪ e ⟫ ⟫))
                  ⋆⟨ 𝓓 ⟩ (transportEq (λ f → 𝓓 [ f B , f C ]) p
                                      (𝓕 ⟪ semG ⟪ e' ⟫ ⟫)))
              ((𝓕 ∘F semG) .F-seq e e')
              ıϕ
      semH-hom (isSetFExp f g p q i j) =
        𝓓 .isSetHom (semH-hom f)
                    (semH-hom g)
                    (cong semH-hom p)
                    (cong semH-hom q)
                    i
                    j

      semH : Functor FH 𝓓
      semH .F-ob = ıH ._$g_
      semH .F-hom = semH-hom
      semH .F-id = refl
      semH .F-seq f g = refl

      semϕ : Eq (𝓕 ∘F semG) (semH ∘F Fϕ)
      semϕ = pathToEq (FreeCatG.induction (funcComp 𝓕 semG)
                                          (funcComp semH Fϕ)
                                          (GrHom≡ aoo aoe))
        where
        𝓕G = (𝓕 .F-ob ∘f ıG ._$g_)
        Hϕ = (ıH ._$g_ ∘f ϕ)

        aoo-gen : ∀ (v : Node G) f g
                → Eq {A = G .Node → 𝓓 .ob} f g
                → Path _ (f v) (g v)
        aoo-gen v f g = J ((λ f' _ → Path _ (f v) (f' v))) refl
        aoo : (v : Node G)
            → Path _ (((𝓕 ∘F semG) ∘Interp ηG) $g v)
                     (((semH ∘F Fϕ) ∘Interp ηG) $g v)
        aoo v = aoo-gen v 𝓕G Hϕ ıϕ

        aoe : {v w : Node G} (e : G .Edge v w) →
              PathP (λ i → 𝓓 .Hom[_,_] (aoo v i) (aoo w i))
                    (𝓕 ⟪ semG ⟪ ↑ e ⟫ ⟫)
                    (semH ⟪ Fϕ ⟪ ↑ e ⟫ ⟫)
        aoe {v}{w} e = toPathP lem where
          lem : Path _
                (transport (λ i → 𝓓 [ aoo-gen v 𝓕G Hϕ ıϕ i
                                        , aoo-gen w 𝓕G Hϕ ıϕ i ])
                               (𝓕 ⟪ ıG <$g> e ⟫))
                (transportEq   (λ f → 𝓓 [ f v , f w ]) ıϕ (𝓕 ⟪ ıG <$g> e ⟫))
          lem =
            J (λ f p →
                Path _
                     ((transport (λ i → 𝓓 [ aoo-gen v 𝓕G f p i
                                              , aoo-gen w 𝓕G f p i ])
                                     (𝓕 ⟪ ıG <$g> e ⟫)))
                     ((transportEq (λ f → 𝓓 [ f v , f w ]) p
                                   (𝓕 ⟪ ıG <$g> e ⟫))))
              (transportRefl (𝓕 ⟪ ıG <$g> e ⟫))
              ıϕ

      module Uniqueness (arb𝓒 : Functor FG 𝓒)
                        (arb𝓓 : Functor FH 𝓓)
                        (arb𝓕 : Path (Functor FG 𝓓) (𝓕 ∘F arb𝓒) (arb𝓓 ∘F Fϕ))
                        (arb𝓒-agree : arb𝓒 ∘Interp ηG ≡ ıG)
                        (arb𝓓-agree : arb𝓓 ∘Interp ηH ≡ ıH)
                        (arb𝓕-agree : Square {A = G .Node → 𝓓 .ob}
                                        (λ i x → arb𝓕 i ⟅ x ⟆)
                                        (eqToPath ıϕ)
                                        (λ i x → 𝓕 ⟅ arb𝓒-agree i $g x ⟆)
                                        (λ i x → arb𝓓-agree i $g (ϕ x)))
             where
        sem-uniq-G : arb𝓒 ≡ semG
        sem-uniq-G = FreeCatG.Semantics.sem-uniq _ _ arb𝓒-agree

        sem-uniq-H : arb𝓓 ≡ semH
        sem-uniq-H = Functor≡ aoo aom where
          aoo : (v : H .Node) → arb𝓓 ⟅ v ⟆ ≡ ıH $g v
          aoo = (λ v i → arb𝓓-agree i $g v)

          aom-type : ∀ {v w} → (f : FH [ v , w ]) → Type _
          aom-type {v}{w} f = PathP (λ i → 𝓓 [ aoo v i , aoo w i ])
                                    (arb𝓓 ⟪ f ⟫)
                                    (semH ⟪ f ⟫)

          aom-id : ∀ {v} → aom-type {v} idₑ
          aom-id = arb𝓓 .F-id ◁ λ i → 𝓓 .id

          aom-seq : ∀ {v w x} → {f : FH [ v , w ]} {g : FH [ w , x ]}
                  → aom-type f
                  → aom-type g
                  → aom-type (f ⋆ₑ g)
          aom-seq hypf hypg = arb𝓓 .F-seq _ _ ◁ λ i → hypf i ⋆⟨ 𝓓 ⟩ hypg i
          ıϕp = eqToPath ıϕ

          aom-F : ∀ {v w}
                → (e : FG [ v , w ])
                → PathP (λ i → 𝓓 [ (arb𝓓-agree i $g (ϕ v))
                                 , (arb𝓓-agree i $g (ϕ w)) ])
                        (arb𝓓 ⟪ Fϕ ⟪ e ⟫ ⟫)
                        (transportEq (λ (f : G .Node → 𝓓 .ob) → 𝓓 [ f v , f w ])
                                     ıϕ
                                     (𝓕 ⟪ semG ⟪ e ⟫ ⟫))
          aom-F {v}{w} e =
            pathified ▷ eqToPath (
              substPath≡transport'
                (λ (f : G .Node → 𝓓 .ob) → 𝓓 [ f v , f w ])
                (𝓕 ⟪ semG ⟪ e ⟫ ⟫)
                ıϕ)
            where
              pathified :
                PathP (λ i → 𝓓 [ arb𝓓-agree i $g ϕ v , arb𝓓-agree i $g ϕ w ])
                      (arb𝓓 ⟪ Fϕ ⟪ e ⟫ ⟫)
                      (transport (λ i → 𝓓 [ ıϕp i v , ıϕp i w ])
                                     (𝓕 ⟪ semG ⟪ e ⟫ ⟫))
              pathified = toPathP⁻ ((
                fromPathP⁻ lem'
                ∙ cong (transport⁻ (λ i → 𝓓 [ arb𝓕 (~ i) ⟅ v ⟆
                                            , arb𝓕 (~ i) ⟅ w ⟆ ]))
                       (fromPathP⁻ lem𝓒)
                ∙ sym (transportComposite
                        ((λ i → 𝓓 [ 𝓕 ⟅ arb𝓒-agree (~ i) $g v ⟆
                                  , 𝓕 ⟅ arb𝓒-agree (~ i) $g w ⟆  ]))
                        (λ i → 𝓓 [ arb𝓕 i ⟅ v ⟆ , arb𝓕 i ⟅ w ⟆  ])
                        ((𝓕 ⟪ semG ⟪ e ⟫ ⟫)))
                ∙ ((λ i → transport (substOf-sems-agreeϕ i) (𝓕 ⟪ semG ⟪ e ⟫ ⟫)))
                ∙ transportComposite
                    (λ i → 𝓓 [ ıϕp i v , ıϕp i w ])
                    (λ i → 𝓓 [ arb𝓓-agree (~ i) $g ϕ v
                             , arb𝓓-agree (~ i) $g ϕ w ])
                    (𝓕 ⟪ semG ⟪ e ⟫ ⟫)
                ))
                where
                  lem' : PathP (λ i → 𝓓 [ arb𝓕 (~ i) ⟅ v ⟆
                                        , arb𝓕 (~ i) ⟅ w ⟆  ])
                           (arb𝓓 ⟪ Fϕ ⟪ e ⟫ ⟫)
                           (𝓕 ⟪ arb𝓒 ⟪ e ⟫ ⟫)
                  lem' i = arb𝓕 (~ i) ⟪ e ⟫

                  lem𝓒 : PathP (λ i → 𝓓 [ 𝓕 ⟅ arb𝓒-agree i $g v ⟆
                                        , 𝓕 ⟅ arb𝓒-agree i $g w ⟆ ])
                           (𝓕 ⟪ arb𝓒 ⟪ e ⟫ ⟫)
                           (𝓕 ⟪ semG ⟪ e ⟫ ⟫)
                  lem𝓒 i = 𝓕 ⟪ sem-uniq-G i ⟪ e ⟫ ⟫

                  substOf-sems-agreeϕ :
                    ((λ i → 𝓓 [ 𝓕 ⟅ arb𝓒-agree (~ i) $g v ⟆
                               , 𝓕 ⟅ arb𝓒-agree (~ i) $g w ⟆ ])
                    ∙ (λ i → 𝓓 [ arb𝓕 i ⟅ v ⟆ , arb𝓕 i ⟅ w ⟆ ]))
                    ≡ ((λ i → 𝓓 [ ıϕp i v , ıϕp i w ])
                      ∙ (λ i → 𝓓 [ arb𝓓-agree (~ i) $g ϕ v
                                 , arb𝓓-agree (~ i) $g ϕ w ]))
                  substOf-sems-agreeϕ =
                    sym (cong-∙ A (λ i x → 𝓕 ⟅ arb𝓒-agree (~ i) $g x ⟆)
                                λ i x → arb𝓕 i ⟅ x ⟆)
                    ∙ cong (cong A)
                           (Square→compPath λ i j x → arb𝓕-agree (~ i) j x)
                    ∙ cong-∙ A (λ i x → ıϕp i x)
                             (λ i x → arb𝓓-agree (~ i) $g ϕ x) where
                      the-type = (G .Node → 𝓓 .ob)
                      A = (λ (f : the-type) → 𝓓 [ f v , f w ])
          aom : ∀ {v w : H .Node} (f : FH [ v , w ]) → aom-type f
          aom (↑ x) = λ i → arb𝓓-agree i <$g> x
          aom idₑ = aom-id
          aom (f ⋆ₑ g) = aom-seq (aom f) (aom g)
          aom F⟪ x ⟫ = aom-F x
          aom (⋆ₑIdL f i) =
            isSet→SquareP
              (λ i j → 𝓓 .isSetHom)
              (aom-seq aom-id (aom f))
              (aom f)
              (λ i → arb𝓓 ⟪ ⋆ₑIdL f i ⟫)
              (λ i → (semH ⟪ ⋆ₑIdL f i ⟫))
              i
          aom (⋆ₑIdR f i) =
            isSet→SquareP (λ i j → 𝓓 .isSetHom)
              (aom-seq (aom f) aom-id)
              (aom f )
              (λ i → arb𝓓 ⟪ ⋆ₑIdR f i ⟫)
              (λ i → semH ⟪ ⋆ₑIdR f i ⟫)
              i
          aom (⋆ₑAssoc f f₁ f₂ i) =
              isSet→SquareP
                (λ i j → 𝓓 .isSetHom)
                (aom-seq (aom-seq (aom f) (aom f₁)) (aom f₂))
                (aom-seq (aom f) (aom-seq (aom f₁) (aom f₂)))
                (λ i → arb𝓓 ⟪ ⋆ₑAssoc f f₁ f₂ i ⟫)
                (λ i → semH ⟪ ⋆ₑAssoc f f₁ f₂ i ⟫)
                i
          aom (F-idₑ i) =
            isSet→SquareP
              (λ i j → 𝓓 .isSetHom)
              (aom-F idₑ)
              aom-id
              (λ i → arb𝓓 ⟪ F-idₑ i ⟫)
              (λ i → semH ⟪ F-idₑ i ⟫)
              i
          aom (F-seqₑ f g i) =
            isSet→SquareP
              (λ i j → 𝓓 .isSetHom)
              (aom-F (f ⋆ₑ g))
              (aom-seq (aom-F f) (aom-F g))
              (λ i → arb𝓓 ⟪ F-seqₑ f g i ⟫)
              (λ i → semH ⟪ F-seqₑ f g i ⟫)
              i
          aom (isSetFExp f f₁ x y i j) k =
            isSet→SquareP
              (λ i j → (isOfHLevelPathP {A = λ k → 𝓓 [ aoo _ k , aoo _ k ]} 2
                                        (𝓓 .isSetHom)
                                        (arb𝓓 ⟪ isSetFExp f f₁ x y i j ⟫)
                                        ((semH ⟪ isSetFExp f f₁ x y i j ⟫))))
              (λ j k → aom (x j) k)
              (λ j k → aom (y j) k)
              (λ i k → aom f k)
              (λ i k → aom f₁ k)
              i j k
