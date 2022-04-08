-- Properties of (pre)additive categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Additive.Properties where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Categories.Additive.Base
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level


-- Some useful lemmas about preadditive categories
module PreaddCategoryTheory (C : PreaddCategory ℓ ℓ') where
  open PreaddCategory C

  -- Pure group theory lemmas
  +idl = λ {x y} → AbGroupStr.lid (homAbStr x y)
  +idr = λ {x y} → AbGroupStr.rid (homAbStr x y)
  +invl = λ {x y} → AbGroupStr.invl (homAbStr x y)
  +invr = λ {x y} → AbGroupStr.invr (homAbStr x y)
  +assoc = λ {x y} → AbGroupStr.assoc (homAbStr x y)
  +comm = λ {x y} → AbGroupStr.comm (homAbStr x y)

  -dist+ : {x y : ob} (f g : Hom[ x , y ]) →
      - (f + g) ≡ (- f) + (- g)
  -dist+ {x} {y} f g =
    let open GroupTheory (AbGroup→Group (Hom[ x , y ] , homAbStr x y)) in
      (invDistr _ _) ∙ (+comm _ _)

  +4assoc : {x y : ob} (a b c d : Hom[ x , y ]) →
      (a + b) + (c + d)  ≡  a + (b + c) + d
  +4assoc a b c d = sym (+assoc _ _ _) ∙ cong (a +_) (+assoc _ _ _)

  +4comm : {x y : ob} (a b c d : Hom[ x , y ]) →
      (a + b) + (c + d)  ≡  (a + c) + (b + d)
  +4comm a b c d = +4assoc _ _ _ _ ∙
      cong (λ u → a + (u + d)) (+comm _ _) ∙ sym (+4assoc _ _ _ _)


  -- Interaction of categorical & group structure
  ⋆0hl : ∀ {w x y} (f : Hom[ x , y ]) → 0h ⋆ f ≡ 0h {w}
  ⋆0hl f =
      0h ⋆ f                              ≡⟨ sym (+idr _) ⟩
      0h ⋆ f  +  0h                       ≡⟨ cong (0h ⋆ f +_) (sym (+invr _)) ⟩
      0h ⋆ f  +  (0h ⋆ f  -  0h ⋆ f)      ≡⟨ +assoc _ _ _ ⟩
      (0h ⋆ f  +  0h ⋆ f)  -  0h ⋆ f      ≡⟨ cong (_- 0h ⋆ f) (sym (⋆distr+ _ _ _)) ⟩
      (0h + 0h) ⋆ f  -  0h ⋆ f            ≡⟨ cong (λ a → a ⋆ f - 0h ⋆ f) (+idr _) ⟩
      0h ⋆ f  -  0h ⋆ f                   ≡⟨ +invr _ ⟩
      0h                                  ∎

  ⋆0hr : ∀ {x y z} (f : Hom[ x , y ]) → f ⋆ 0h ≡ 0h {x} {z}
  ⋆0hr f =
      f ⋆ 0h                              ≡⟨ sym (+idr _) ⟩
      f ⋆ 0h  +  0h                       ≡⟨ cong (f ⋆ 0h +_) (sym (+invr _)) ⟩
      f ⋆ 0h  +  (f ⋆ 0h  -  f ⋆ 0h)      ≡⟨ +assoc _ _ _ ⟩
      (f ⋆ 0h  +  f ⋆ 0h)  -  f ⋆ 0h      ≡⟨ cong (_- f ⋆ 0h) (sym (⋆distl+ _ _ _)) ⟩
      f ⋆ (0h + 0h)  -  f ⋆ 0h            ≡⟨ cong (λ a → f ⋆ a - f ⋆ 0h) (+idr _) ⟩
      f ⋆ 0h  -  f ⋆ 0h                   ≡⟨ +invr _ ⟩
      0h                                  ∎

  -distl⋆ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ])
    → (- f) ⋆ g ≡ - (f ⋆ g)
  -distl⋆ {x} {y} {z} f g =
    let open GroupTheory (AbGroup→Group (Hom[ x , z ] , homAbStr x z)) in
    invUniqueR (
      f ⋆ g + (- f) ⋆ g     ≡⟨ sym (⋆distr+ _ _ _) ⟩
      (f - f) ⋆ g           ≡⟨ cong (_⋆ g) (+invr _) ⟩
      0h ⋆ g                ≡⟨ ⋆0hl _ ⟩
      0h                    ∎
    )

  -distr⋆ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ])
    → f ⋆ (- g) ≡ - (f ⋆ g)
  -distr⋆ {x} {y} {z} f g =
    let open GroupTheory (AbGroup→Group (Hom[ x , z ] , homAbStr x z)) in
    invUniqueR (
      f ⋆ g + f ⋆ (- g)     ≡⟨ sym (⋆distl+ _ _ _) ⟩
      f ⋆ (g - g)           ≡⟨ cong (f ⋆_) (+invr _) ⟩
      f ⋆ 0h                ≡⟨ ⋆0hr _ ⟩
      0h                    ∎
    )


-- Matrix notation for morphisms  (x₁ ⊕ ⋯ ⊕ x­­ₙ) → (y₁ ⊕ ⋯ ⊕ yₘ)
-- in an additive category
module MatrixNotation (A : AdditiveCategory ℓ ℓ') where
    open AdditiveCategory A
    open PreaddCategoryTheory preaddcat

    -- Polymorphic biproduct morphisms
    i₁ = λ {x y} → Biproduct.i₁ (biprod x y)
    i₂ = λ {x y} → Biproduct.i₂ (biprod x y)
    π₁ = λ {x y} → Biproduct.π₁ (biprod x y)
    π₂ = λ {x y} → Biproduct.π₂ (biprod x y)
    -- and axioms
    i₁⋆π₁ = λ {x y} → Biproduct.i₁⋆π₁ (biprod x y)
    i₁⋆π₂ = λ {x y} → Biproduct.i₁⋆π₂ (biprod x y)
    i₂⋆π₁ = λ {x y} → Biproduct.i₂⋆π₁ (biprod x y)
    i₂⋆π₂ = λ {x y} → Biproduct.i₂⋆π₂ (biprod x y)
    ∑π⋆i  = λ {x y} → Biproduct.∑π⋆i  (biprod x y)


    _∣_ : ∀ {x y y'} → Hom[ x , y ] → Hom[ x , y' ] → Hom[ x , y ⊕ y' ]
    f ∣ f' = (f ⋆ i₁) + (f' ⋆ i₂)
    infixr 5 _∣_

    _`_ : ∀ {y y' z} → Hom[ y , z ] → Hom[ y' , z ] → Hom[ y ⊕ y' , z ]
    g ` g' = (π₁ ⋆ g) + (π₂ ⋆ g')
    infixr 6 _`_


    -- Use the matrix notation like this:
    private module _ (x y : ob) (f : Hom[ x , y ]) where

      h : Hom[ x ⊕ x ⊕ x , y ⊕ y ⊕ y ⊕ y ]

      h =  f  ` - f `  0h   ∣
           0h `  0h `  f    ∣
           f  ` - f `  0h   ∣
           0h `  f  ` f + f


    -- Exchange law
    exchange : ∀ {x x' y y'} (a : Hom[ x , y ]) (b : Hom[ x' , y ])
            (c : Hom[ x , y' ]) (d : Hom[ x' , y' ]) →
        (a ` b ∣ c ` d)  ≡  (a ∣ c) ` (b ∣ d)

    exchange a b c d =
        (π₁ ⋆ a  +  π₂ ⋆ b) ⋆ i₁  +  (π₁ ⋆ c  +  π₂ ⋆ d) ⋆ i₂
                ≡⟨ cong₂ _+_ (⋆distr+ _ _ _) (⋆distr+ _ _ _) ⟩
        ((π₁ ⋆ a) ⋆ i₁  +  (π₂ ⋆ b) ⋆ i₁)  +  ((π₁ ⋆ c) ⋆ i₂  +  (π₂ ⋆ d) ⋆ i₂)
                ≡⟨ +4comm _ _ _ _ ⟩
        ((π₁ ⋆ a) ⋆ i₁  +  (π₁ ⋆ c) ⋆ i₂)  +  ((π₂ ⋆ b) ⋆ i₁  +  (π₂ ⋆ d) ⋆ i₂)
                ≡⟨ cong₂ _+_ (cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _))
                            (cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _)) ⟩
        (π₁ ⋆ (a ⋆ i₁)  +  π₁ ⋆ (c ⋆ i₂))  +  (π₂ ⋆ (b ⋆ i₁)  +  π₂ ⋆ (d ⋆ i₂))
                ≡⟨ sym (cong₂ _+_ (⋆distl+ _ _ _) (⋆distl+ _ _ _)) ⟩
        π₁ ⋆ (a ⋆ i₁  +  c ⋆ i₂)  +  π₂ ⋆ (b ⋆ i₁  +  d ⋆ i₂)
                ∎


    -- iₖ times a row
    module _ {x x' y : ob} (a : Hom[ x , y ]) (b : Hom[ x' , y ]) where

      i₁⋆row :  i₁ ⋆ (a ` b)  ≡  a
      i₁⋆row =
          i₁ ⋆ (π₁ ⋆ a  +  π₂ ⋆ b)
                  ≡⟨ ⋆distl+ _ _ _ ⟩
          i₁ ⋆ (π₁ ⋆ a)  +  i₁ ⋆ (π₂ ⋆ b)
                  ≡⟨ cong₂ _+_ (sym (⋆Assoc _ _ _)) (sym (⋆Assoc _ _ _)) ⟩
          (i₁ ⋆ π₁) ⋆ a  +  (i₁ ⋆ π₂) ⋆ b
                  ≡⟨ cong₂ (λ u v → u ⋆ a + v ⋆ b) i₁⋆π₁ i₁⋆π₂ ⟩
          id ⋆ a  +  0h ⋆ b
                  ≡⟨ cong₂ _+_ (⋆IdL _) (⋆0hl _) ⟩
          a  +  0h
                  ≡⟨ +idr _ ⟩
          a       ∎

      i₂⋆row :  i₂ ⋆ (a ` b)  ≡  b
      i₂⋆row =
          i₂ ⋆ (π₁ ⋆ a  +  π₂ ⋆ b)
                  ≡⟨ ⋆distl+ _ _ _ ⟩
          i₂ ⋆ (π₁ ⋆ a)  +  i₂ ⋆ (π₂ ⋆ b)
                  ≡⟨ cong₂ _+_ (sym (⋆Assoc _ _ _)) (sym (⋆Assoc _ _ _)) ⟩
          (i₂ ⋆ π₁) ⋆ a  +  (i₂ ⋆ π₂) ⋆ b
                  ≡⟨ cong₂ (λ u v → u ⋆ a + v ⋆ b) i₂⋆π₁ i₂⋆π₂ ⟩
          0h ⋆ a  +  id ⋆ b
                  ≡⟨ cong₂ _+_ (⋆0hl _) (⋆IdL _) ⟩
          0h  +  b
                  ≡⟨ +idl _ ⟩
          b       ∎


    -- A column times πₖ
    module _ {x y y' : ob} (a : Hom[ x , y ]) (b : Hom[ x , y' ]) where

      col⋆π₁ :  (a ∣ b) ⋆ π₁  ≡  a
      col⋆π₁ =
          (a ⋆ i₁  +  b ⋆ i₂) ⋆ π₁
                  ≡⟨ ⋆distr+ _ _ _ ⟩
          (a ⋆ i₁) ⋆ π₁  +  (b ⋆ i₂) ⋆ π₁
                  ≡⟨ cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _) ⟩
          a ⋆ (i₁ ⋆ π₁)  +  b ⋆ (i₂ ⋆ π₁)
                  ≡⟨ cong₂ (λ u v → a ⋆ u + b ⋆ v) i₁⋆π₁ i₂⋆π₁ ⟩
          a ⋆ id  +  b ⋆ 0h
                  ≡⟨ cong₂ _+_ (⋆IdR _) (⋆0hr _) ⟩
          a  +  0h
                  ≡⟨ +idr _ ⟩
          a       ∎

      col⋆π₂ :  (a ∣ b) ⋆ π₂  ≡  b
      col⋆π₂ =
          (a ⋆ i₁  +  b ⋆ i₂) ⋆ π₂
                  ≡⟨ ⋆distr+ _ _ _ ⟩
          (a ⋆ i₁) ⋆ π₂  +  (b ⋆ i₂) ⋆ π₂
                  ≡⟨ cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _) ⟩
          a ⋆ (i₁ ⋆ π₂)  +  b ⋆ (i₂ ⋆ π₂)
                  ≡⟨ cong₂ (λ u v → a ⋆ u + b ⋆ v) i₁⋆π₂ i₂⋆π₂ ⟩
          a ⋆ 0h  +  b ⋆ id
                  ≡⟨ cong₂ _+_ (⋆0hr _) (⋆IdR _) ⟩
          0h  +  b
                  ≡⟨ +idl _ ⟩
          b       ∎

    -- iₖ / πₖ times a diagonal matrix
    module _ {x x' y y'} (a : Hom[ x , y ]) (b : Hom[ x' , y' ]) where

      i₁⋆diag :  i₁ ⋆ (a ` 0h ∣ 0h ` b)  ≡  a ⋆ i₁
      i₁⋆diag =
          i₁ ⋆ (a ` 0h ∣ 0h ` b)          ≡⟨ cong (i₁ ⋆_) (exchange _ _ _ _) ⟩
          i₁ ⋆ ((a ∣ 0h) ` (0h ∣ b))      ≡⟨ i₁⋆row _ _ ⟩
          (a ∣ 0h)                        ≡⟨ cong (a ⋆ i₁ +_) (⋆0hl _) ⟩
          a ⋆ i₁  +  0h                   ≡⟨ +idr _ ⟩
          a ⋆ i₁                          ∎

      i₂⋆diag :  i₂ ⋆ (a ` 0h ∣ 0h ` b)  ≡  b ⋆ i₂
      i₂⋆diag =
          i₂ ⋆ (a ` 0h ∣ 0h ` b)          ≡⟨ cong (i₂ ⋆_) (exchange _ _ _ _) ⟩
          i₂ ⋆ ((a ∣ 0h) ` (0h ∣ b))      ≡⟨ i₂⋆row _ _ ⟩
          (0h ∣ b)                        ≡⟨ cong (_+ b ⋆ i₂) (⋆0hl _) ⟩
          0h  +  b ⋆ i₂                   ≡⟨ +idl _ ⟩
          b ⋆ i₂                          ∎

      diag⋆π₁ :  (a ` 0h ∣ 0h ` b) ⋆ π₁  ≡  π₁ ⋆ a
      diag⋆π₁ =
          (a ` 0h ∣ 0h ` b) ⋆ π₁      ≡⟨ col⋆π₁ _ _ ⟩
          a ` 0h                      ≡⟨ cong (π₁ ⋆ a +_) (⋆0hr _) ⟩
          π₁ ⋆ a  +  0h               ≡⟨ +idr _ ⟩
          π₁ ⋆ a                      ∎

      diag⋆π₂ :  (a ` 0h ∣ 0h ` b) ⋆ π₂  ≡  π₂ ⋆ b
      diag⋆π₂ =
          (a ` 0h ∣ 0h ` b) ⋆ π₂      ≡⟨ col⋆π₂ _ _ ⟩
          0h ` b                      ≡⟨ cong (_+ π₂ ⋆ b) (⋆0hr _) ⟩
          0h  +  π₂ ⋆ b               ≡⟨ +idl _ ⟩
          π₂ ⋆ b                      ∎


    -- Matrix addition
    addRow : ∀ {x y z}
        (f f' : Hom[ x , z ]) (g g' : Hom[ y , z ]) →
        (f ` g) + (f' ` g') ≡ (f + f') ` (g + g')

    addRow f f' g g' =
        (π₁ ⋆ f + π₂ ⋆ g) + (π₁ ⋆ f' + π₂ ⋆ g')
                ≡⟨ +4comm _ _ _ _ ⟩
        (π₁ ⋆ f + π₁ ⋆ f') + (π₂ ⋆ g + π₂ ⋆ g')
                ≡⟨ sym (cong₂ _+_ (⋆distl+ _ _ _) (⋆distl+ _ _ _)) ⟩
        π₁ ⋆ (f + f') + π₂ ⋆ (g + g')
                ∎

    addCol : ∀ {x y z}
        (f f' : Hom[ x , y ]) (g g' : Hom[ x , z ]) →
        (f ∣ g) + (f' ∣ g') ≡ (f + f') ∣ (g + g')

    addCol f f' g g' =
        (f ⋆ i₁ + g ⋆ i₂) + (f' ⋆ i₁ + g' ⋆ i₂)
                ≡⟨ +4comm _ _ _ _ ⟩
        (f ⋆ i₁ + f' ⋆ i₁) + (g ⋆ i₂ + g' ⋆ i₂)
                ≡⟨ sym (cong₂ _+_ (⋆distr+ _ _ _) (⋆distr+ _ _ _)) ⟩
        (f + f') ⋆ i₁ + (g + g') ⋆ i₂
                ∎


    private
      ⋆4assoc : ∀ {x y z w v} (a : Hom[ x , y ]) (b : Hom[ y , z ])
              (c : Hom[ z , w ]) (d : Hom[ w , v ]) →
          (a ⋆ b) ⋆ (c ⋆ d) ≡ a ⋆ (b ⋆ c) ⋆ d
      ⋆4assoc a b c d = (⋆Assoc _ _ _) ∙ cong (a ⋆_) (sym (⋆Assoc _ _ _))

      ⋆4assoc' : ∀ {x y z w v} (a : Hom[ x , y ]) (b : Hom[ y , z ])
              (c : Hom[ z , w ]) (d : Hom[ w , v ]) →
          (a ⋆ b) ⋆ (c ⋆ d) ≡ (a ⋆ (b ⋆ c)) ⋆ d
      ⋆4assoc' a b c d = sym (⋆Assoc _ _ _) ∙ cong (_⋆ d) (⋆Assoc _ _ _)


    -- Matrix multiplication
    innerProd : ∀ {x y₁ y₂ z} (f₁ : Hom[ x , y₁ ]) (g₁ : Hom[ y₁ , z ])
                              (f₂ : Hom[ x , y₂ ]) (g₂ : Hom[ y₂ , z ]) →
        (f₁ ∣ f₂) ⋆ (g₁ ` g₂) ≡ (f₁ ⋆ g₁) + (f₂ ⋆ g₂)

    innerProd f₁ g₁ f₂ g₂ =
        (f₁ ⋆ i₁ + f₂ ⋆ i₂) ⋆ (π₁ ⋆ g₁ + π₂ ⋆ g₂)
                ≡⟨ ⋆distr+ _ _ _ ⟩
        (f₁ ⋆ i₁) ⋆ (π₁ ⋆ g₁ + π₂ ⋆ g₂)  +  (f₂ ⋆ i₂) ⋆ (π₁ ⋆ g₁ + π₂ ⋆ g₂)
                ≡⟨ cong₂ _+_ (⋆distl+ _ _ _) (⋆distl+ _ _ _) ⟩
        ((f₁ ⋆ i₁) ⋆ (π₁ ⋆ g₁)  +  (f₁ ⋆ i₁) ⋆ (π₂ ⋆ g₂))
            +  (f₂ ⋆ i₂) ⋆ (π₁ ⋆ g₁)  +  (f₂ ⋆ i₂) ⋆ (π₂ ⋆ g₂)
                ≡⟨ cong₂ _+_ (cong₂ _+_ eq₁₁ eq₁₂) (cong₂ _+_ eq₂₁ eq₂₂) ⟩
        (f₁ ⋆ g₁  +  0h)  +  0h  +  f₂ ⋆ g₂
                ≡⟨ cong₂ _+_ (+idr _) (+idl _) ⟩
        (f₁ ⋆ g₁) + (f₂ ⋆ g₂)
                ∎
     where
      eq₁₁ = (f₁ ⋆ i₁) ⋆ (π₁ ⋆ g₁)      ≡⟨ ⋆4assoc _ _ _ _ ⟩
             f₁ ⋆ (i₁ ⋆ π₁) ⋆ g₁        ≡⟨ cong (λ u → _ ⋆ u ⋆ _) i₁⋆π₁ ⟩
             f₁ ⋆ id ⋆ g₁               ≡⟨ cong (f₁ ⋆_) (⋆IdL _) ⟩
             f₁ ⋆ g₁                    ∎

      eq₁₂ = (f₁ ⋆ i₁) ⋆ (π₂ ⋆ g₂)      ≡⟨ ⋆4assoc _ _ _ _ ⟩
             f₁ ⋆ (i₁ ⋆ π₂) ⋆ g₂        ≡⟨ cong (λ u → _ ⋆ u ⋆ _) i₁⋆π₂ ⟩
             f₁ ⋆ 0h ⋆ g₂               ≡⟨ cong (f₁ ⋆_) (⋆0hl _) ⟩
             f₁ ⋆ 0h                    ≡⟨ ⋆0hr _ ⟩
             0h                         ∎

      eq₂₁ = (f₂ ⋆ i₂) ⋆ (π₁ ⋆ g₁)      ≡⟨ ⋆4assoc _ _ _ _ ⟩
             f₂ ⋆ (i₂ ⋆ π₁) ⋆ g₁        ≡⟨ cong (λ u → _ ⋆ u ⋆ _) i₂⋆π₁ ⟩
             f₂ ⋆ 0h ⋆ g₁               ≡⟨ cong (f₂ ⋆_) (⋆0hl _) ⟩
             f₂ ⋆ 0h                    ≡⟨ ⋆0hr _ ⟩
             0h                         ∎

      eq₂₂ = (f₂ ⋆ i₂) ⋆ (π₂ ⋆ g₂)      ≡⟨ ⋆4assoc _ _ _ _ ⟩
             f₂ ⋆ (i₂ ⋆ π₂) ⋆ g₂        ≡⟨ cong (λ u → _ ⋆ u ⋆ _) i₂⋆π₂ ⟩
             f₂ ⋆ id ⋆ g₂               ≡⟨ cong (f₂ ⋆_) (⋆IdL _) ⟩
             f₂ ⋆ g₂                    ∎


    outerProd : ∀ {x₁ x₂ y z₁ z₂} (f₁ : Hom[ x₁ , y ]) (g₁ : Hom[ y , z₁ ])
                                  (f₂ : Hom[ x₂ , y ]) (g₂ : Hom[ y , z₂ ]) →

        (f₁ ` f₂) ⋆ (g₁ ∣ g₂)  ≡  f₁ ⋆ g₁ ` f₂ ⋆ g₁ ∣
                                  f₁ ⋆ g₂ ` f₂ ⋆ g₂

    outerProd {y = y} f₁ g₁ f₂ g₂ =
        (π₁ ⋆ f₁  +  π₂ ⋆ f₂) ⋆ (g₁ ⋆ i₁  +  g₂ ⋆ i₂)
                ≡⟨ ⋆distl+ _ _ _ ⟩
        (π₁ ⋆ f₁  +  π₂ ⋆ f₂) ⋆ (g₁ ⋆ i₁)  +  (π₁ ⋆ f₁  +  π₂ ⋆ f₂) ⋆ (g₂ ⋆ i₂)
                ≡⟨ cong₂ _+_ (eq g₁ i₁) (eq g₂ i₂) ⟩
           (π₁ ⋆ (f₁ ⋆ g₁)  +  π₂ ⋆ (f₂ ⋆ g₁)) ⋆ i₁
        +  (π₁ ⋆ (f₁ ⋆ g₂)  +  π₂ ⋆ (f₂ ⋆ g₂)) ⋆ i₂
                ∎
     where
      eq = λ {z w} (g : Hom[ y , z ]) (i : Hom[ z , w ]) →
        (π₁ ⋆ f₁  +  π₂ ⋆ f₂) ⋆ (g ⋆ i)
                ≡⟨ ⋆distr+ _ _ _ ⟩
        (π₁ ⋆ f₁) ⋆ (g ⋆ i)  +  (π₂ ⋆ f₂) ⋆ (g ⋆ i)
                ≡⟨ cong₂ _+_ (⋆4assoc' _ _ _ _) (⋆4assoc' _ _ _ _) ⟩
        (π₁ ⋆ (f₁ ⋆ g)) ⋆ i  +  (π₂ ⋆ (f₂ ⋆ g)) ⋆ i
                ≡⟨ sym (⋆distr+ _ _ _) ⟩
        (π₁ ⋆ (f₁ ⋆ g)  +  π₂ ⋆ (f₂ ⋆ g)) ⋆ i
                    ∎
