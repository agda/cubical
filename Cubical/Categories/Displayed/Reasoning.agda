{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

module Cubical.Categories.Displayed.Reasoning
  {ℓC ℓ'C ℓCᴰ ℓ'Cᴰ : Level}
  {C : Category ℓC ℓ'C}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓ'Cᴰ)
  where

  open Categoryᴰ Cᴰ
  private module C = Category C
  open Category hiding (_∘_)

  reind : {a b : C.ob} {f g : C [ a , b ]} (p : f ≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → Hom[ f ][ aᴰ , bᴰ ] → Hom[ g ][ aᴰ , bᴰ ]
  reind p = subst Hom[_][ _ , _ ] p

  reind-filler : {a b : C.ob} {f g : C [ a , b ]} (p : f ≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (f : Hom[ f ][ aᴰ , bᴰ ])
    → f ≡[ p ] reind p f
  reind-filler p = subst-filler Hom[_][ _ , _ ] p

  reind-filler-sym : {a b : C.ob} {f g : C [ a , b ]} (p : f ≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (f : Hom[ g ][ aᴰ , bᴰ ])
    → reind (sym p) f ≡[ p ] f
  reind-filler-sym p = symP ∘ reind-filler (sym p)

  ≡[]-rectify : {a b : C.ob} {f g : C [ a , b ]} {p p' : f ≡ g}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
    → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
  ≡[]-rectify {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡[_] gᴰ) (C.isSetHom _ _ _ _)

  ≡[]∙ : {a b : C.ob} {f g h : C [ a , b ]}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
      {hᴰ : Hom[ h ][ aᴰ , bᴰ ]}
      (p : f ≡ g) (q : g ≡ h)
    → fᴰ ≡[ p ] gᴰ
    → gᴰ ≡[ q ] hᴰ → fᴰ ≡[ p ∙ q ] hᴰ
  ≡[]∙ {fᴰ = fᴰ} {hᴰ = hᴰ} p q eq1 eq2 =
    subst
      (λ p → PathP (λ i → p i) fᴰ hᴰ)
      (sym $ congFunct Hom[_][ _ , _ ] p q)
      (compPathP eq1 eq2)

  infixr 30 ≡[]∙
  syntax ≡[]∙ p q eq1 eq2 = eq1 [ p ]∙[ q ] eq2

  ≡[]⋆ : {a b c : C.ob} {f g : C [ a , b ]} {h i : C [ b , c ]}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]} {cᴰ : ob[ c ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
      {hᴰ : Hom[ h ][ bᴰ , cᴰ ]}
      {iᴰ : Hom[ i ][ bᴰ , cᴰ ]}
      (p : f ≡ g) (q : h ≡ i)
    → fᴰ ≡[ p ] gᴰ → hᴰ ≡[ q ] iᴰ → fᴰ ⋆ᴰ hᴰ ≡[ cong₂ C._⋆_ p q ] gᴰ ⋆ᴰ iᴰ
  ≡[]⋆ _ _ = congP₂ (λ _ → _⋆ᴰ_)

  infixr 30 ≡[]⋆
  syntax ≡[]⋆ p q eq1 eq2 = eq1 [ p ]⋆[ q ] eq2

  reind-rectify : {a b : C.ob} {f g : C [ a , b ]} {p p' : f ≡ g}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
    → reind p fᴰ ≡ reind p' fᴰ
  reind-rectify {fᴰ = fᴰ} = cong (λ p → reind p fᴰ) (C.isSetHom _ _ _ _)

  reind-contractʳ : {a b c : C.ob} {f g : C [ a , b ]} {h : C [ b , c ]}
      {p : f ≡ g}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]} {cᴰ : ob[ c ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]} {hᴰ : Hom[ h ][ bᴰ , cᴰ ]}
    → reind (cong (C._⋆ h) p) (fᴰ ⋆ᴰ hᴰ) ≡ reind p fᴰ ⋆ᴰ hᴰ
  reind-contractʳ {hᴰ = hᴰ} = fromPathP $
    congP (λ _ → _⋆ᴰ hᴰ) (transport-filler _ _)

  reind-comp : {a b : C.ob} {f g h : C [ a , b ]} {p : f ≡ g} {q : g ≡ h}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
    → reind (p ∙ q) fᴰ ≡ reind q (reind p fᴰ)
  reind-comp = substComposite Hom[_][ _ , _ ] _ _ _

  reind-contractˡ : {a b c : C.ob} {f : C [ a , b ]} {g h : C [ b , c ]}
      {p : g ≡ h}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]} {cᴰ : ob[ c ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]} {gᴰ : Hom[ g ][ bᴰ , cᴰ ]}
    → reind (cong (f C.⋆_) p) (fᴰ ⋆ᴰ gᴰ) ≡ fᴰ ⋆ᴰ reind p gᴰ
  reind-contractˡ {fᴰ = fᴰ} = fromPathP $
    congP (λ _ → fᴰ ⋆ᴰ_) (transport-filler _ _)

  ≡→≡[] : {a b : C.ob} {f g : C [ a , b ]} {p : f ≡ g}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
    → reind p fᴰ ≡ gᴰ → fᴰ ≡[ p ] gᴰ
  ≡→≡[] = toPathP
