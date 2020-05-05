{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Frame where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP     renaming (SNS-≡ to SNS)
open import Cubical.Structures.Poset
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv   hiding (_■)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Family

-- We will adopt the convention of referring using ℓ₀, ℓ₁, ℓ₂ for the
-- carrier level, relation level, and the index type level respectively
private
  variable
    ℓ₀ ℓ₁ ℓ₂ : Level

-- TODO: is this defined somewhere?
uncurry : ∀ {A : Type ℓ₀} {B : A → Type ℓ₁} {C : Σ A B → Type ℓ₂} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

module JoinSyntax (A : Type ℓ₀) {ℓ₂ : Level} (join : Fam ℓ₂ A → A) where

  join-of : {I : Type ℓ₂} → (I → A) → A
  join-of {I = I} f = join (I , f)

  syntax join-of (λ i → e) = ⋁⟨ i ⟩ e

RawFrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type _
RawFrameStr ℓ₁ ℓ₂ A = PosetStr ℓ₁ A × A × (A → A → A) × (Fam ℓ₂ A → A)

isTop : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → hProp (ℓ-max ℓ₀ ℓ₁)
isTop P x = ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ]) , isPropΠ λ y → snd (y ⊑[ P ] x)

isGLB : (P : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp (ℓ-max ℓ₀ ℓ₁)
isGLB P _∧_ = ∧-GLB , ∧-GLB-prop
  where
    ∧-GLB = -- x ∧ y is a lower bound of {x, y}.
        ((x y    : ∣ P ∣ₚ) → [ (x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y ])
        -- Given any other lower bound z of {x, y}, x ∧ y is _greater_ than that.
      × ((x y z  : ∣ P ∣ₚ) → [ (z ⊑[ P ] x ⊓ z ⊑[ P ] y) ⇒  z ⊑[ P ] (x ∧ y) ])

    ∧-GLB-prop : isProp ∧-GLB
    ∧-GLB-prop =
      isPropΣ
        (isPropΠ2 λ x y → snd ((x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y)) λ _ →
        isPropΠ3 λ x y z → snd (z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] (x ∧ y))

isLUB : (P : Poset ℓ₀ ℓ₁) → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp _
isLUB {ℓ₂ = ℓ₂} P ⋁_ = ⋁-LUB , ⋁-LUB-prop
  where
    ⋁-LUB = ((U : Fam ℓ₂ ∣ P ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ P ] (⋁ U)) ])
          × ((U : Fam ℓ₂ ∣ P ∣ₚ) (x : _) → [ (∀[ y ε U ] (y ⊑[ P ] x)) ⇒ (⋁ U) ⊑[ P ] x ])

    ⋁-LUB-prop : isProp ⋁-LUB
    ⋁-LUB-prop = isPropΣ
                   (λ ψ ϑ → funExt λ U →
                     snd (∀[ y ε U ] (y ⊑[ P ] (⋁ U))) (ψ U) (ϑ U)) λ _ →
                   isPropΠ λ U → isPropΠ λ x →
                     snd (∀[ y ε U ] (y ⊑[ P ] x) ⇒ (⋁ U) ⊑[ P ] x)

isDist : (P : Poset ℓ₀ ℓ₁)
       → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ)
       → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ)
       → hProp _
isDist {ℓ₂ = ℓ₂} P _⊓_ ⋁_ = ∧-dist-over-⋁ , ∧-dist-over-⋁-prop
  where
    open JoinSyntax ∣ P ∣ₚ ⋁_

    ∧-dist-over-⋁ = (x : ∣ P ∣ₚ) (U : Fam ℓ₂ ∣ P ∣ₚ) → x ⊓ (⋁ U) ≡ ⋁⟨ i ⟩ (x ⊓ (U $ i))

    ∧-dist-over-⋁-prop : isProp ∧-dist-over-⋁
    ∧-dist-over-⋁-prop p q = funExt2 λ x U → carrier-is-set P _ _ (p x U) (q x U)

FrameAx : {A : Type ℓ₀} → RawFrameStr ℓ₁ ℓ₂ A → hProp _
FrameAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = A} (s@(_⊑_ , _) , ⊤ , _∧_ , ⋁_) =
  isTop P ⊤ ⊓ isGLB P _∧_ ⊓ isLUB P ⋁_ ⊓ isDist P _∧_ ⋁_
  where
    P : Poset ℓ₀ ℓ₁
    P = A , s

FrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type _
FrameStr ℓ₁ ℓ₂ = add-to-structure (RawFrameStr ℓ₁ ℓ₂) λ _ RF → [ FrameAx RF ]

Frame : (ℓ₀ ℓ₁ ℓ₂ : Level) → Type _
Frame ℓ₀ ℓ₁ ℓ₂ = Σ (Type ℓ₀) (FrameStr ℓ₁ ℓ₂)

-- Projection for the carrier set of a frame
-- i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Type ℓ₀
∣ A , _ ∣F = A

-- The underlying poset of a frame.
pos : Frame ℓ₀ ℓ₁ ℓ₂ → Poset ℓ₀ ℓ₁
pos (A , (P , _) , _) = A , P

-- Projections for the top element, meet, and join of a frame.

⊤[_] : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F
⊤[ _ , (_ , (⊤ , _)) , _ ] = ⊤

glb-of : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
glb-of (_ , (_ , _ , _⊓_ , _) , _) = _⊓_

syntax glb-of F x y = x ⊓[ F ] y

⋁[_]_ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Fam ℓ₂ ∣ F ∣F → ∣ F ∣F
⋁[ (_ , (_ , (_ , _ , ⋁_)) , _) ] U = ⋁ U

-- Projections for frame laws.

module _ (F : Frame ℓ₀ ℓ₁ ℓ₂) where
  private
    P = pos F

    _⊑_ : ∣ F ∣F → ∣ F ∣F → hProp ℓ₁
    x ⊑ y = x ⊑[ P ] y

    open JoinSyntax ∣ F ∣F (λ - → ⋁[ F ] -)

  ⊤[_]-top : (x : ∣ F ∣F) → [ x ⊑ ⊤[ F ] ]
  ⊤[_]-top = let (_ , _ , frame-str) = F in fst frame-str

  ⊓[_]-lower₀ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ x ]
  ⊓[_]-lower₀ = let (_ , _ , str) = F in λ x y → fst (fst (fst (snd str)) x y)


  ⊓[_]-lower₁ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ y ]
  ⊓[_]-lower₁ = let (_ , _ , str) = F in λ x y → snd (fst (fst (snd str)) x y)

  ⊓[_]-greatest : (x y z : ∣ F ∣F) → [ z ⊑ x ] → [ z ⊑ y ] → [ z ⊑ (x ⊓[ F ] y) ]
  ⊓[_]-greatest =
    let (_ , _ , str) = F in λ x y z z⊑x z⊑y → snd (fst (snd str)) x y z (z⊑x , z⊑y)

  ⋁[_]-upper : (U : Fam ℓ₂ ∣ F ∣F) (o : ∣ F ∣F) → o ε U → [ o ⊑ (⋁[ F ] U) ]
  ⋁[_]-upper = let (_ , _ , str) = F in fst (fst (snd (snd str)))

  ⋁[_]-least : (U : Fam ℓ₂ ∣ F ∣F) (x : ∣ F ∣F)
             → [ ∀[ y ε U ] (y ⊑ x) ] → [ (⋁[ F ] U) ⊑ x ]
  ⋁[_]-least = let (_ , _ , str) = F in snd (fst (snd (snd str)))

  dist : (x : ∣ F ∣F) (U : Fam ℓ₂ ∣ F ∣F)
       → x ⊓[ F ] (⋁⟨ i ⟩ (U $ i)) ≡ ⋁⟨ i ⟩ (x ⊓[ F ] (U $ i))
  dist = let (_ , _ , str) = F in snd (snd (snd str))

  top-unique : (y : ∣ F ∣F) → ((x : ∣ F ∣F) → [ x ⊑ y ]) → y ≡ ⊤[ F ]
  top-unique y y-top = ⊑[ pos F ]-antisym y ⊤[ F ] (⊤[_]-top y) (y-top ⊤[ F ])

  ⊓-unique : (x y z : ∣ F ∣F)
           → [ z ⊑ x ] → [ z ⊑ y ] → ((w : ∣ F ∣F) → [ w ⊑ x ] → [ w ⊑ y ] → [ w ⊑ z ])
           → z ≡ x ⊓[ F ] y
  ⊓-unique x y z z⊑x z⊑y greatest =
    ⊑[ P ]-antisym z (x ⊓[ F ] y) (⊓[_]-greatest x y z z⊑x z⊑y) NTS
    where
      NTS : [ (x ⊓[ F ] y) ⊑ z ]
      NTS = greatest (x ⊓[ F ] y) (⊓[_]-lower₀ x y) (⊓[_]-lower₁ x y)

  ⋁-unique : (U : Fam ℓ₂ ∣ F ∣F) (z : ∣ F ∣F)
           → ((x : ∣ F ∣F) → x ε U → [ x ⊑ z ])
           → ((w : ∣ F ∣F) → ((o : ∣ F ∣F) → o ε U → [ o ⊑ w ]) → [ z ⊑ w ])
           → z ≡ ⋁[ F ] U
  ⋁-unique U z upper least =
    ⊑[ P ]-antisym z (⋁[ F ] U) (least (⋁[ F ] U) (⋁[_]-upper U)) NTS
    where
      NTS : [ (⋁[ F ] U) ⊑ z ]
      NTS = ⋁[_]-least U z upper

  comm : (x y : ∣ F ∣F) → x ⊓[ F ] y ≡ y ⊓[ F ] x
  comm x y = ⊓-unique y x _ (⊓[_]-lower₁ x y) (⊓[_]-lower₀ x y) NTS
    where
      NTS = λ w w⊑y w⊑x → ⊓[_]-greatest x y w w⊑x w⊑y

  family-iff : {U V : Fam ℓ₂ ∣ F ∣F}
             → ((x : ∣ F ∣F) → (x ε U → x ε V) × (x ε V → x ε U))
             → ⋁[ F ] U ≡ ⋁[ F ] V
  family-iff {U = U} {V = V} h = ⋁-unique _ _ ub least
    where
      ub : (o : ∣ F ∣F) → o ε V → [ o ⊑ (⋁[ F ] U) ]
      ub o (i , p) =
        subst (λ - → [ - ⊑ _ ]) p (⋁[ _ ]-upper _ (snd (h (V $ i)) (i , refl)))

      least : (w : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ε V → [ o ⊑ w ])
            → [ (⋁[ F ] U) ⊑ w ]
      least w f = ⋁[ _ ]-least _ λ o oεU → f o (fst (h o) oεU)

  flatten : (I : Type ℓ₂) (J : I → Type ℓ₂) (f : (i : I) → J i → ∣ F ∣F)
          → ⋁[ F ] (Σ I J , uncurry f) ≡ ⋁[ F ] ⁅ ⋁[ F ] (J i , λ j → f i j) ∣ i ∶ I ⁆
  flatten I J f = ⊑[ pos F ]-antisym _ _ down up
    where
      open PosetReasoning (pos F)

      LHS = ⋁[ F ] (Σ I J , uncurry f)
      RHS = ⋁[ F ] (I , (λ i → ⋁[ F ] (J i , f i)))

      down : [ LHS ⊑ RHS ]
      down = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F) → x ε (Σ I J , uncurry f) → [ x ⊑ RHS ]
          isUB x ((i , j) , eq) =
              x                          ⊑⟨ ≡⇒⊑ (pos F) (sym eq)      ⟩
              f i j                      ⊑⟨ ⋁[_]-upper _ _ (j , refl) ⟩
              ⋁[ F ] (J i , λ - → f i -) ⊑⟨ ⋁[_]-upper _ _ (i , refl) ⟩
              RHS                        ■

      up : [ RHS ⊑ LHS ]
      up = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F)
               → x ε ⁅ ⋁[ F ] (J i , f i) ∣ i ∶ I ⁆ → [ x ⊑ (⋁[ F ] (Σ I J , uncurry f)) ]
          isUB x (i , p) =
            x                          ⊑⟨ ≡⇒⊑ (pos F) (sym p)  ⟩
            ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ⊑⟨ ⋁[_]-least _ _ isUB′ ⟩
            ⋁[ F ] (Σ I J , uncurry f) ■
            where
              isUB′ : (z : ∣ F ∣F) → z ε ⁅ f i j ∣ j ∶ J i ⁆ → [ z ⊑ LHS ]
              isUB′ z (j , q) = ⋁[_]-upper _ _ ((i , j) , q)

  sym-distr : (U@(I , _) V@(J , _) : Fam ℓ₂ ∣ F ∣F)
            → (⋁⟨ i ⟩ (U $ i)) ⊓[ F ] (⋁⟨ i ⟩ (V $ i))
            ≡ ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
  sym-distr U@(I , _) V@(J , _) =
    (⋁[ F ] U) ⊓[ F ] (⋁[ F ] V)
      ≡⟨ dist (⋁[ F ] U) V ⟩
    ⋁[ F ] ((λ - → (⋁[ F ] U) ⊓[ F ] -) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₀ ⟩
    ⋁[ F ] ((λ x → x ⊓[ F ] (⋁[ F ] U)) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₁ ⟩
    ⋁[ F ] ((λ x → ⋁[ F ] ((λ y → x ⊓[ F ] y) ⟨$⟩ U)) ⟨$⟩ V)
      ≡⟨ sym (flatten (index V) (λ _ → index U) λ j i →  (V $ j) ⊓[ F ] (U $ i))  ⟩
    ⋁[ F ] ⁅ (V $ j) ⊓[ F ] (U $ i) ∣ (j , i) ∶ (J × I) ⁆
      ≡⟨ family-iff NTS₂  ⟩
    ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
      ∎
    where
      open PosetReasoning (pos F)

      NTS₀ : (λ - → (⋁[ F ] U) ⊓[ F ] -) ≡ (λ - → - ⊓[ F ] (⋁[ F ] U))
      NTS₀ = funExt λ x → comm (⋁[ F ] U) x

      NTS₁ : (λ - → - ⊓[ F ] (⋁[ F ] U)) ≡ (λ - → ⋁[ F ] ((λ y → - ⊓[ F ] y) ⟨$⟩ U))
      NTS₁ = funExt λ x → dist x U

      NTS₂ : _
      NTS₂ x = down , up
        where
          down : _
          down ((j , i) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (i′ , j′) → comm (V $ j′) (U $ i′) })) ((i , j) , eq)

          up : _
          up ((i , j) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (j′ , i′) → comm (U $ i′) (V $ j′) })) ((j , i) , eq)

RF-iso : {ℓ₁ ℓ₂ : Level} (M N : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂))
       → fst M ≃ fst N → Type _
RF-iso {ℓ₂ = ℓ₂} (A , (P , _) , ⊤₀ , _⊓₀_ , ⋁₀) (B , (Q , _), ⊤₁ , _⊓₁_ , ⋁₁) i =
    (order-iso (A , P) (B , Q) i)
  × (f ⊤₀ ≡ ⊤₁)
  × ((x y : A) → f (x ⊓₀ y) ≡ (f x) ⊓₁ (f y))
  × ((U : Fam ℓ₂ A) → f (⋁₀ U) ≡ ⋁₁ (f ⟨$⟩ U))
  where
    f = equivFun i

pos-of : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂) → Σ (Type ℓ₀) (Order ℓ₁)
pos-of (A , ((RPS , _) , _)) = (A , RPS)

top-of : (F : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂)) → fst F
top-of (_ , _ , ⊤ , _) = ⊤

RF-is-SNS : SNS {ℓ₀} (RawFrameStr ℓ₁ ℓ₂) RF-iso
RF-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {X = A} F@(P , ⊤₀ , _⊓₀_ , ⋁₀) G@(Q , ⊤₁ , _⊓₁_ , ⋁₁) =
  f , f-equiv
  where
    C = RawFrameStr ℓ₁ ℓ₂ A

    _⊑₀_ : A → A → hProp ℓ₁
    x ⊑₀ y = x ⊑[ (A , P) ] y

    _⊑₁_ : A → A → hProp ℓ₁
    x ⊑₁ y = x ⊑[ (A , Q) ] y

    A-set₀ = carrier-is-set (A , P)

    PS-A = fst P
    PS-B = fst Q

    f : RF-iso (A , F) (A , G) (idEquiv A) → F ≡ G
    f (iₚ , eq-⊤ , ⊓-xeq , ⋁-xeq) =
      P , ⊤₀ , _⊓₀_ , ⋁₀   ≡⟨ cong (λ - → (P , - , _⊓₀_ , ⋁₀))              eq-⊤ ⟩
      P , ⊤₁ , _⊓₀_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → P , ⊤₁ , - , ⋁₀)    ⊓-eq ⟩
      P , ⊤₁ , _⊓₁_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → P , ⊤₁ , _⊓₁_ , -)  ⋁-eq ⟩
      P , ⊤₁ , _⊓₁_ , ⋁₁   ≡⟨ cong {B = λ _ → C} (λ - → - , ⊤₁ , _⊓₁_ , ⋁₁) eq   ⟩
      Q , ⊤₁ , _⊓₁_ , ⋁₁   ∎
      where
        eq : P ≡ Q
        eq = ΣProp≡
               (poset-ax-props A)
               (funExt λ x → funExt λ y → ⇔toPath (fst (iₚ x y)) (snd (iₚ x y)))

        ⊓-eq : _⊓₀_ ≡ _⊓₁_
        ⊓-eq = funExt (λ x → funExt λ y → ⊓-xeq x y)

        ⋁-eq : ⋁₀ ≡ ⋁₁
        ⋁-eq = funExt λ U → ⋁-xeq U

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , ret eq) , h eq }
      where
        g : (eq : F ≡ G) → RF-iso (A , F) (A , G) (idEquiv A)
        g eq = φ , ψ , ϑ , ξ
          where
            𝒻  = equivFun (idEquiv A)

            φ : order-iso (A , _⊑₀_) (A , _⊑₁_) (idEquiv A)
            φ x y =
                (subst (λ { ((_⊑⋆_ , _) , _) → [ x ⊑⋆ y ] }) eq)
              , subst (λ { ((_⊑⋆_ , _) , _) → [ x ⊑⋆ y ] }) (sym eq)

            ψ : equivFun (idEquiv A) ⊤₀ ≡ ⊤₁
            ψ = subst (λ { (_ , - , _ , _) → 𝒻 - ≡ ⊤₁ }) (sym eq) refl

            ϑ : (x y : A) → 𝒻 (x ⊓₀ y) ≡ (𝒻 x) ⊓₁ (𝒻 y)
            ϑ x y =
              subst (λ { (_ , _ , _-_ , _) → 𝒻 (x - y) ≡ (𝒻 x) ⊓₁ (𝒻 y) }) (sym eq) refl

            ξ : (U : Fam ℓ₂ A) → 𝒻 (⋁₀ U) ≡ ⋁₁ (index U , λ i → 𝒻 (U $ i))
            ξ U = subst (λ { (_ , _ , _ , -) → 𝒻 (- U) ≡ ⋁₁ (𝒻 ⟨$⟩ U) }) (sym eq) refl

        str-set : isSet (RawFrameStr ℓ₁ ℓ₂ A)
        str-set = isSetΣ (PosetStr-set ℓ₁ A) λ _ →
                  isSetΣ A-set₀ λ _ →
                  isSetΣ (isSetΠ λ _ → isSetΠ λ _ → A-set₀) λ _ → isSetΠ λ _ → A-set₀

        ret : (eq : F ≡ G) → f (g eq) ≡ eq
        ret eq = str-set F G (f (g eq)) eq

        RF-iso-prop : isProp (RF-iso (A , F) (A , G) (idEquiv A))
        RF-iso-prop =
          isPropΣ (RP-iso-prop (A , fst P) (A , fst Q) (idEquiv A)) (λ _ →
          isPropΣ (λ p q → A-set₀ _ _ p q ) λ _ →
          isPropΣ (isPropΠ λ _ → isPropΠ λ _ → A-set₀ _ _) λ _ →
          isPropΠ λ _ → A-set₀ _ _)

        h : (eq : F ≡ G) → (fib : fiber f eq) → (g eq , ret eq) ≡ fib
        h eq (i , p) =
          ΣProp≡ (λ x → isOfHLevelSuc 2 str-set F G (f x) eq) (RF-iso-prop (g eq) i)

