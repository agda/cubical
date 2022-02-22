{-# OPTIONS --safe #-}

module Cubical.HITs.Delooping.Group where

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.Group.Instances.SetsAutomorphism

open import Cubical.Homotopy.Group.Base

variable
  ℓ : Level


ΣPathPProp≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
           → ∀ {a}
           → {u : (B a)}
           → (q : (a : A) → isProp (B a))
           → (ΣPathPProp  {A = λ x → A} {B = λ _ x → B x} {u = a , u} {v = a , u} q refl) ≡ refl
fst (ΣPathPProp≡ {a = a} q i i₁) = a
snd (ΣPathPProp≡ {B = B} {a = a} {u = u} q i i₁) =
    hcomp (λ k →
            λ { (i = i1) → u
              ; (i₁ = i0) → u
              ; (i₁ = i1) → q a (transp (λ i₂ → B a) i0 u) u (k ∨ i)
              })
           {!!}
          -- (transportRefl u i)

-- i = i0 ⊢ hcomp
--          (λ { j (i₁ = i0) → u
--             ; j (i₁ = i1) → q a (transp (λ i₂ → B a) i0 u) u j
--             })
--          (transp (λ j → B a) (~ i₁) u)
-- i = i1 ⊢ u
-- i₁ = i0 ⊢ u
-- i₁ = i1 ⊢ u

module _ (G : Group ℓ) where

  open GroupStr (snd G) renaming (assoc to assocG)

  open GroupTheory G

  isSet-⟨G⟩ = (isSetGroup G)

  data B[_] : Type ℓ where
    base : B[_]
    loop : ⟨ G ⟩ → base ≡ base
    loop1 : loop 1g ≡ refl
    loopInv : ∀ g → loop (inv g) ≡ sym (loop g)  
    loop· : ∀ (g x : ⟨ G ⟩)
        → PathP (λ i → base ≡ loop g i) (loop (x · (inv g))) (loop x)
    trunc : isGroupoid B[_]

  private
    variable
      ℓ' : Level
      A : Type ℓ'


  module Elim where
    rec : (x : A)
        → (p : ⟨ G ⟩ → x ≡ x)
        → p 1g ≡ refl
        → (∀ g → (p (inv g)) ≡ sym (p g))
        → (sq : ∀ (g x' : ⟨ G ⟩)
             → PathP (λ i → x ≡ p g i) (p (x' · (inv g))) (p x'))
        → isGroupoid A
        → B[_] → A
    rec x p x₁ x₂ sq x₃ = go
      where
        go : _ → _
        go base = x
        go (loop x i) = p x i
        go (loop1 i i₁) = x₁ i i₁
        go (loopInv g i i₁) = x₂ g i i₁
        go (loop· g₁ g₂ i i₁) = sq g₁ g₂ i i₁
        go (trunc x x₁ x₂ y x₃' y₁ i i₁ x₄) =
          x₃ (go x) (go x₁) (cong go x₂) (cong go y) (cong (cong go) x₃') (cong (cong go) y₁) i i₁ x₄

    elim : ∀ {ℓ'} (P : B[_] → Type ℓ')
         → (x : P base)
         → (p : (g : ⟨ G ⟩) → PathP (λ i → P (loop g i)) x x)
         → SquareP (λ i i₁ → P (loop1 i i₁)) (p 1g ) refl refl refl
         → (∀ g → SquareP (λ i i₁ → P (loopInv g i i₁)) (p (inv g)) (λ i₁ → p g (~ i₁)) refl refl )
         → (∀ g₁ g₂ → SquareP (λ i i₁ → P (loop· g₁ g₂ i i₁)) (p (g₂ · inv g₁)) (p g₂) refl (p g₁) )
         → isOfHLevelDep 3 P
         → (z : B[_]) → P z
    elim P x p x₁ x₂ x₃ x₄ = go
      where
        go : ∀ z → _
        go base = x
        go (loop x i) = p x i
        go (loop1 i i₁) = x₁ i i₁
        go (loopInv g i i₁) = x₂ g i i₁
        go (loop· g₁ g₂ i i₁) = x₃ g₁ g₂ i i₁
        go (trunc x x₁ x₂ y x₃' y₁ i i₁ x₄') =
          x₄ (go x) (go x₁) (cong go x₂) (cong go y) (cong (cong go) x₃') (cong (cong go) y₁)
            (trunc x x₁ x₂ y x₃' y₁ )
            i i₁ x₄'

    elimSet : ∀ {ℓ'} (P : B[_] → Type ℓ')
         → (x : P base)
         → (p : (g : ⟨ G ⟩) → PathP (λ i → P (loop g i)) x x)
         → isOfHLevelDep 2 P
         → (z : B[_]) → P z
    elimSet P x p Pset =
      elim P x p
        (toPathP (Pset _ _ _ _ _))
        (λ _ → toPathP (Pset _ _ _ _ _))
        (λ _ _ → toPathP (Pset _ _ _ _ _))
        (isOfHLevelDepSuc 2 Pset)

    Code : B[_] → hSet ℓ
    Code =
      rec (⟨ G ⟩ , isSet-⟨G⟩)
          (λ g → w' (isoToPath (fst (G→SetAut⟨G⟩ G) g)))
          p1
          p2
          p3
          (isOfHLevelTypeOfHLevel 2)
      where
       w : _
       w = invEq≡→equivFun≡ (Σ≡PropEquiv (λ _ → isPropIsSet))

       w≡ : (a b : _≡_ {A = hSet ℓ} (fst G , isSet-⟨G⟩) (fst G , isSet-⟨G⟩))
             → transport (cong fst a) ≡ transport (cong fst b)   
             → a ≡ b
       w≡ a b x =
         let z = isInjectiveTransport x

             zz : PathP (λ z₁ → _≡_ {A = hSet ℓ} (fst (a z₁) , snd (a z₁)) (fst (b z₁) , snd (b z₁))) _ _
             zz = λ i → ΣPathPProp (λ _ → isPropIsSet) λ i₁ → z i₁ i

             ppp0 : _
             ppp0 = ΣPathPProp≡ (λ _ → isPropIsSet)

             ppp1 : _
             ppp1 = ΣPathPProp≡ (λ _ → isPropIsSet)

         in transport (λ i → PathP (λ x₁ → ppp0 i x₁ ≡ ppp1 i x₁) a b)
                      (λ i i₁ → ((fst (zz i₁ i)) , snd (zz i₁ i)))
           
         
       w' : (fst G ≡ fst G) → ((fst G , isSet-⟨G⟩) ≡ (fst G , isSet-⟨G⟩))
       w' = equivFun (Σ≡PropEquiv (λ z → isPropIsSet {A = z}) {fst G , isSet-⟨G⟩} {fst G , isSet-⟨G⟩})

       p1 : _
       p1 = w (isInjectiveTransport (funExt (cong (transport refl) ∘ sym ∘ rid)))

       p2 : _
       p2 g = w (isInjectiveTransport (funExt λ x → cong (_· _) (transportRefl _) ∙ sym (transportRefl _)))

       p3 : _
       p3 g x' = toPathP (fromPathP (compPath-filler _ _)
         ∙ w≡ _ _
            (funExt λ x → cong (transport refl)
               (cong (_· g) (transportRefl _ ∙ cong (_· (x' · inv g)) (transportRefl x))
                 ∙ sym (assocG _ _ _) ∙ cong (x ·_) (sym (assocG _ _ _) ∙ cong (x' ·_) (invl g) ∙ rid x'))))


    El : B[_] → Type ℓ
    El b = Code b .fst


    encode : ∀ x → base ≡ x → El x
    encode x p = transport (cong El p) 1g 

    decodeSq : ∀ g → PathP (λ i → El (loop g i) → base ≡ loop g i) loop loop
    decodeSq g i x j =
      hcomp (λ k →
                  λ { (i = i0) →
                         let p' = sym (assocG x g (inv g)) ∙ cong (x ·_) (invr g) ∙ rid x
                         in (cong loop p') k j
                    ; (i = i1) → loop x j
                    ; (j = i0) → base
                    ; (j = i1) → loop g i})
           (loop· g (unglue (i ∨ ~ i) x) i j)

    decode : (x : B[_]) → El x → base ≡ x
    decode = elimSet _
      loop
      decodeSq
      (isOfHLevel→isOfHLevelDep 2
       λ _ → isOfHLevelΠ 2 λ _ → trunc base _)
      

    ΩB[_]-Iso-⟨G⟩ : Iso ⟨ G ⟩ (base ≡ base) 
    Iso.fun ΩB[_]-Iso-⟨G⟩ = loop
    Iso.inv ΩB[_]-Iso-⟨G⟩ = encode base
    Iso.rightInv ΩB[_]-Iso-⟨G⟩ =
       J (λ y x →  decode y (encode y x) ≡ x) (cong loop (transportRefl _) ∙ loop1)
    Iso.leftInv ΩB[_]-Iso-⟨G⟩ _ = transportRefl _ ∙ lid _

    ΩB[_] : Group ℓ
    ΩB[_] = (base ≡ base) , groupstr refl _∙_ sym
       (makeIsGroup (trunc _ _) assoc  (λ x → sym (rUnit x)) (λ x → sym (lUnit x)) rCancel lCancel)

    loop-isHom : GroupEquiv G ΩB[_] 
    fst loop-isHom = loop , isoToIsEquiv ΩB[_]-Iso-⟨G⟩ 
    IsGroupHom.pres· (snd loop-isHom) x y =
             cong (loop ∘ (x ·_) )(sym (invInv y))
           ∙ sym (fromPathP (symP (loop· (inv y) x)))
           ∙ fromPathP (compPath-filler (loop x) (λ i → loop (inv y) (~ i)))
           ∙ (λ j i →
                   hcomp
                     (doubleComp-faces (λ _ → base) (sym (loopInv y j)) i)
                      (loop x i))
    IsGroupHom.pres1 (snd loop-isHom) = loop1 
    IsGroupHom.presinv (snd loop-isHom) = loopInv
