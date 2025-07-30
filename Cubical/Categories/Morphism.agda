module Cubical.Categories.Morphism where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category


private
  variable
    ℓ ℓ' : Level

-- C needs to be explicit for these definitions as Agda can't infer it
module _ (C : Category ℓ ℓ') where
  open Category C

  private
    variable
      x y z v w : ob

  isMonic : Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
  isMonic {x} {y} f =
    ∀ {z} {a a' : Hom[ z , x ]} → f ∘ a ≡ f ∘ a' → a ≡ a'

  isPropIsMonic : (f : Hom[ x , y ]) → isProp (isMonic f)
  isPropIsMonic _ = isPropImplicitΠ (λ _ → (isPropImplicitΠ2
    (λ a a' → (isProp→ (isOfHLevelPath' 1 isSetHom a a')))))

  postcompCreatesMonic : (f : Hom[ x , y ]) (g : Hom[ y , z ])
    → isMonic (f ⋆ g) → isMonic f
  postcompCreatesMonic f g monic {a = a} {a' = a'} fa≡fa' =
    monic (sym (⋆Assoc a f g) ∙ cong (_⋆ g) fa≡fa' ∙ ⋆Assoc a' f g)

  monicComp : (f : Hom[ x , y ]) (g : Hom[ y , z ])
    → isMonic f → isMonic g → isMonic (f ⋆ g)
  monicComp f g mon-f mon-g {a = a} {a' = a'} eq =
    mon-f (mon-g (⋆Assoc a f g ∙ eq ∙ sym (⋆Assoc a' f g)))

  monicId : {x : ob} → isMonic (id {x})
  monicId {a = a} {a' = a'} eq = sym (⋆IdR a) ∙ eq ∙ ⋆IdR a'

  retraction⇒monic : (f : Hom[ x , y ]) (lInv : Hom[ y , x ])
    → (lInv ∘ f ≡ id) → isMonic f
  retraction⇒monic f lInv eq =
    postcompCreatesMonic f lInv (subst isMonic (sym eq) monicId)

  isEpic : (Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
  isEpic {x} {y} g =
    ∀ {z} {b b' : Hom[ y , z ]} → b ∘ g ≡ b' ∘ g → b ≡ b'

  isPropIsEpic : (f : Hom[ x , y ]) → isProp (isEpic f)
  isPropIsEpic _ = isPropImplicitΠ (λ _ → (isPropImplicitΠ2
    (λ a a' → (isProp→ (isOfHLevelPath' 1 isSetHom a a')))))

  precompCreatesEpic : (f : Hom[ x , y ]) (g : Hom[ z , x ])
    → isEpic (g ⋆ f) → isEpic f
  precompCreatesEpic f g epic {b = b} {b' = b'} bf≡b'f =
    epic (⋆Assoc g f b ∙ cong (g ⋆_) bf≡b'f ∙ sym (⋆Assoc g f b'))

  -- A morphism is split monic if it has a *retraction*
  isSplitMon : (Hom[ x , y ]) → Type ℓ'
  isSplitMon {x} {y} f = ∃[ r ∈ Hom[ y , x ] ] r ∘ f ≡ id

  -- A morphism is split epic if it has a *section*
  isSplitEpi : (Hom[ x , y ]) → Type ℓ'
  isSplitEpi {x} {y} g = ∃[ s ∈ Hom[ y , x ] ] g ∘ s ≡ id

  record areInv (f : Hom[ x , y ]) (g : Hom[ y , x ]) : Type ℓ' where
    field
      sec : g ⋆ f ≡ id
      ret : f ⋆ g ≡ id

  open areInv

  isPropAreInv : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} → isProp (areInv f g)
  isPropAreInv a b i .sec = isSetHom _ _ (a .sec) (b .sec) i
  isPropAreInv a b i .ret = isSetHom _ _ (a .ret) (b .ret) i

-- C can be implicit here
module _ {C : Category ℓ ℓ'} where
  open Category C

  private
    variable
      x y z v w : ob

  open areInv

  symAreInv : {f : Hom[ x , y ]} {g : Hom[ y , x ]} → areInv C f g → areInv C g f
  sec (symAreInv x) = ret x
  ret (symAreInv x) = sec x

  -- equational reasoning with inverses
  invMoveR : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} {h : Hom[ z , x ]} {k : Hom[ z , y ]}
           → areInv C f g
           → h ⋆ f ≡ k
           → h ≡ k ⋆ g
  invMoveR {f = f} {g} {h} {k} ai p
    = h
    ≡⟨ sym (⋆IdR _) ⟩
      (h ⋆ id)
    ≡⟨ cong (h ⋆_) (sym (ai .ret)) ⟩
      (h ⋆ (f ⋆ g))
    ≡⟨ sym (⋆Assoc _ _ _) ⟩
      ((h ⋆ f) ⋆ g)
    ≡⟨ cong (_⋆ g) p ⟩
      k ⋆ g
    ∎

  invMoveL : ∀ {f : Hom[ x , y ]} {g : Hom[ y , x ]} {h : Hom[ y , z ]} {k : Hom[ x , z ]}
          → areInv C f g
          → f ⋆ h ≡ k
          → h ≡ g ⋆ k
  invMoveL {f = f} {g} {h} {k} ai p
    = h
    ≡⟨ sym (⋆IdL _) ⟩
      id ⋆ h
    ≡⟨ cong (_⋆ h) (sym (ai .sec)) ⟩
      (g ⋆ f) ⋆ h
    ≡⟨ ⋆Assoc _ _ _ ⟩
      g ⋆ (f ⋆ h)
    ≡⟨ cong (g ⋆_) p ⟩
      (g ⋆ k)
    ∎

  invFlipSq : {f₁⁻¹ : Hom[ x , y ]} {f₁ : Hom[ y , x ]}
              {f₂⁻¹ : Hom[ v , w ]} {f₂ : Hom[ w , v ]}
              {g : Hom[ x , v ]} {h : Hom[ y , w ]}
            → areInv C f₁ f₁⁻¹ → areInv C f₂ f₂⁻¹
            → h ⋆ f₂ ≡ f₁ ⋆ g
            → g ⋆ f₂⁻¹ ≡ f₁⁻¹ ⋆ h
  invFlipSq {f₁⁻¹ = f₁⁻¹} {f₁} {f₂⁻¹} {f₂} {g} {h} inv₁ inv₂ sq =
    g ⋆ f₂⁻¹                ≡⟨ cong (_⋆ f₂⁻¹) (sym (⋆IdL _)) ⟩
    (id ⋆ g) ⋆ f₂⁻¹         ≡⟨ cong (λ m → (m ⋆ g) ⋆ f₂⁻¹) (sym (inv₁ .sec)) ⟩
    ((f₁⁻¹ ⋆ f₁) ⋆ g) ⋆ f₂⁻¹ ≡⟨ cong (_⋆ f₂⁻¹) (⋆Assoc _ _ _) ⟩
    (f₁⁻¹ ⋆ (f₁ ⋆ g)) ⋆ f₂⁻¹ ≡⟨ ⋆Assoc _ _ _ ⟩
    f₁⁻¹ ⋆ ((f₁ ⋆ g) ⋆ f₂⁻¹) ≡⟨ cong (λ m → f₁⁻¹ ⋆ (m ⋆ f₂⁻¹)) (sym sq) ⟩
    f₁⁻¹ ⋆ ((h ⋆ f₂) ⋆ f₂⁻¹) ≡⟨ cong (f₁⁻¹ ⋆_) (⋆Assoc _ _ _) ⟩
    f₁⁻¹ ⋆ (h ⋆ (f₂ ⋆ f₂⁻¹)) ≡⟨ cong (λ m → f₁⁻¹ ⋆ (h ⋆ m)) (inv₂ .ret) ⟩
    f₁⁻¹ ⋆ (h ⋆ id)         ≡⟨ cong (f₁⁻¹ ⋆_) (⋆IdR _) ⟩
    f₁⁻¹ ⋆ h ∎

  open isIso

  isIso→areInv : ∀ {f : Hom[ x , y ]}
               → (isI : isIso C f)
               → areInv C f (isI .inv)
  sec (isIso→areInv isI) = sec isI
  ret (isIso→areInv isI) = ret isI


  -- Back and forth between isIso and CatIso

  isIso→CatIso : ∀ {f : C [ x , y ]}
               → isIso C f
               → CatIso C x y
  isIso→CatIso x = _ , x

  CatIso→isIso : (cIso : CatIso C x y)
               → isIso C (cIso .fst)
  CatIso→isIso = snd

  CatIso→areInv : (cIso : CatIso C x y)
                → areInv C (cIso .fst) (cIso .snd .inv)
  CatIso→areInv cIso = isIso→areInv (CatIso→isIso cIso)

  -- reverse of an iso is also an iso
  symCatIso : ∀ {x y}
             → CatIso C x y
             → CatIso C y x
  symCatIso (mor , isiso inv sec ret) = inv , isiso mor ret sec
