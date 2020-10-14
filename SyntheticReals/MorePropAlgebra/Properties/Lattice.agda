{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_; _$_)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIsProp) renaming (elim to ∣∣-elim)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax to infix  -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix  -4 ∃[∶]-syntax --
  ; ∀[∶]-syntax to infix  -4 ∀[∶]-syntax --
  ; ∀[]-syntax to infix  -4 ∀[]-syntax   --
  )

open import SyntheticReals.Utils
open import SyntheticReals.MorePropAlgebra.Bundles
open import SyntheticReals.MoreLogic.Definitions hiding (≡ˢ-syntax)
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Properties

module SyntheticReals.MorePropAlgebra.Properties.Lattice {ℓ} {ℓ'} (assumptions : Lattice {ℓ} {ℓ'}) where
open Lattice assumptions renaming (Carrier to A)

module OnType where
  abstract
    ≤-reflectsʳ-≡ : ∀ x y → [ (∀[ z ] z ≤ x ⇔ z ≤ y) ⇔ x ≡ₚ y ]
    ≤-reflectsʳ-≡ x y .fst z≤x⇔z≤y    = ≤-antisym x y (z≤x⇔z≤y x .fst (≤-refl x)) (z≤x⇔z≤y y .snd (≤-refl y))
    ≤-reflectsʳ-≡ x y .snd x≡y z .fst = substₚ (λ p → z ≤ p) x≡y
    ≤-reflectsʳ-≡ x y .snd x≡y z .snd = substₚ (λ p → z ≤ p) (symₚ x≡y)

    ≤-reflectsˡ-≡ : ∀ x y → [ (∀[ z ] x ≤ z ⇔ y ≤ z) ⇔ x ≡ₚ y ]
    ≤-reflectsˡ-≡ x y .fst x≤z⇔y≤z    = ≤-antisym x y (x≤z⇔y≤z y .snd (≤-refl y)) (x≤z⇔y≤z x .fst (≤-refl x))
    ≤-reflectsˡ-≡ x y .snd x≡y z .fst = substₚ (λ p → p ≤ z) x≡y
    ≤-reflectsˡ-≡ x y .snd x≡y z .snd = substₚ (λ p → p ≤ z) (symₚ x≡y)

    min-≤ : ∀ x y → [ (min x y ≤ x) ⊓ (min x y ≤ y) ]
    min-≤ x y = is-min x y (min x y) .fst (≤-refl (min x y))

    max-≤ : ∀ x y → [ (x ≤ max x y) ⊓ (y ≤ max x y) ]
    max-≤ x y = is-max x y (max x y) .fst (≤-refl (max x y))

    min-identity-≤ : ∀ x y → [ x ≤ y ] → [ min x y ≡ₚ x ]
    min-identity-≤ x y x≤y = symₚ $ ≤-antisym x (min x y) (is-min x y x .snd (≤-refl x , x≤y)) (min-≤ x y .fst)

    max-identity-≤ : ∀ x y → [ x ≤ y ] → [ max x y ≡ₚ y ]
    max-identity-≤ x y x≤y = symₚ $ ≤-antisym y (max x y) (max-≤ x y .snd) (is-max x y y .snd (x≤y , ≤-refl y))

    -- min-≤-⊔ : ∀ x y z → [ min x y ≤ z ] → [ (x ≤ z) ⊔ (y ≤ z) ]
    -- min-≤-⊔ x y z mxy≤z = {! contraposition (x ≤ y) ⊓ (y ≤ z) (x ≤ z) $ uncurryₚ (x ≤ y) (y ≤ z) (x ≤ z)$ ≤-trans x y z  !}

    min-identity : ∀ x → [ min x x ≡ₚ x ]
    min-identity x =
      let p = is-min x x x .snd (≤-refl x , ≤-refl x)
          q = min-≤ x x .fst
      in ≤-antisym (min x x) x q p

    min-comm : ∀ x y → [ min x y ≡ₚ min y x ]
    min-comm x y = ≤-reflectsʳ-≡ (min x y) (min y x) .fst γ where
      γ : ∀ z → [ (z ≤ min x y) ⇔ (z ≤ min y x) ]
      γ z .fst p = is-min y x z .snd (swap (is-min x y z .fst p))
      γ z .snd p = is-min x y z .snd (swap (is-min y x z .fst p))

    min-assoc : ∀ x y z → [ min (min x y) z ≡ₚ min x (min y z) ]
    min-assoc x y z =  ≤-reflectsʳ-≡ (min (min x y) z) (min x (min y z)) .fst γ where
      γ : ∀ w → [ (w ≤ min (min x y) z) ⇔ (w ≤ min x (min y z)) ]
      γ w .fst p = let (w≤mxy , w≤z) = is-min (min x y) z w .fst p
                       (w≤x   , w≤y) = is-min x y w .fst w≤mxy
                       w≤myz         = is-min y z w .snd (w≤y , w≤z)
                   in  is-min x (min y z) w .snd (w≤x , w≤myz)
      γ w .snd p = let (w≤x , w≤myz) = is-min x (min y z) w .fst p
                       (w≤y , w≤z  ) = is-min y z w .fst w≤myz
                       w≤mxy         = is-min x y w .snd (w≤x , w≤y)
                   in is-min (min x y) z w .snd (w≤mxy , w≤z)

    max-identity : ∀ x → [ max x x ≡ₚ x ]
    max-identity x =
      let p = is-max x x x .snd (≤-refl x , ≤-refl x)
          q = max-≤ x x .fst
      in symₚ $ ≤-antisym x (max x x) q p

    max-comm : ∀ x y → [ max x y ≡ₚ max y x ]
    max-comm x y = ≤-reflectsˡ-≡ (max x y) (max y x) .fst γ where
      γ : ∀ z → [ (max x y ≤ z) ⇔ (max y x ≤ z) ]
      γ z .fst p = is-max y x z .snd (swap (is-max x y z .fst p))
      γ z .snd p = is-max x y z .snd (swap (is-max y x z .fst p))

    max-assoc : ∀ x y z → [ max (max x y) z ≡ₚ max x (max y z) ]
    max-assoc x y z =  ≤-reflectsˡ-≡ (max (max x y) z) (max x (max y z)) .fst γ where
      γ : ∀ w → [ (max (max x y) z ≤ w) ⇔ (max x (max y z)) ≤ w ]
      γ w .fst p = let (mxy≤w , z≤w) = is-max (max x y) z w .fst p
                       (x≤w   , y≤w) = is-max x y w .fst mxy≤w
                       myz≤w         = is-max y z w .snd (y≤w , z≤w)
                   in  is-max x (max y z) w .snd (x≤w , myz≤w)
      γ w .snd p = let (x≤w , myz≤w) = is-max x (max y z) w .fst p
                       (y≤w , z≤w  ) = is-max y z w .fst myz≤w
                       mxy≤w         = is-max x y w .snd (x≤w , y≤w)
                   in is-max (max x y) z w .snd (mxy≤w , z≤w)

    min-max-absorptive : ∀ x y → [ min x (max x y) ≡ₚ x ]
    min-max-absorptive x y = ≤-reflectsʳ-≡ (min x (max x y)) x .fst γ where
      γ : ∀ z → [ (z ≤ min x (max x y)) ⇔ (z ≤ x) ]
      γ z .fst p = is-min x (max x y) z .fst p .fst
      γ z .snd p = is-min x (max x y) z .snd (p , ≤-trans _ _ _ p (max-≤ x y .fst))

    max-min-absorptive : ∀ x y → [ max x (min x y) ≡ₚ x ]
    max-min-absorptive x y = ≤-reflectsˡ-≡ (max x (min x y)) x .fst γ where
      γ : ∀ z → [ (max x (min x y) ≤ z) ⇔ (x ≤ z) ]
      γ z .fst p = is-max x (min x y) z .fst p .fst
      γ z .snd p = is-max x (min x y) z .snd (p , ≤-trans _ _ _ (min-≤ x y .fst) p)

  -- min-split : ∀ x y → [ x ≤ min x y ⊔ y ≤ min x y ]
  -- min-split x y = {! is-min x y x  !}

  -- min-elim : ∀ x y → P x → P y → P (min x y)

  -- w < x + z → w <
  -- w ≤ a + b → w ≤ a ⊔ w ≤ b

  -- also interesting: interaction of max and abs
  --   https://math.stackexchange.com/questions/3149575/max-and-min-inequality

  module +-inv⇒
    (_+_ : A → A → A)
    (0f : A)
    (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
    (+-assoc     : ∀ a b c → [ ((a + b) + c) ≡ₚ (a + (b + c)) ])
    (+-identityʳ : ∀ x → [ (x + 0f) ≡ₚ x ])
    (+-comm      : ∀ a b → [ (a + b) ≡ₚ (b + a) ])
    (+-inv''     : ∀ x → [ ∃[ y ] (x + y) ≡ₚ 0f ])
    where

    ≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ]
    ≤-min-+ a b c w w≤a+c w≤b+c = ∣∣-elim (λ _ → isProp[] (w ≤ (min a b + c))) (λ{ (-c , p) → γ -c p }) (+-inv'' c) where
      γ : ∀ -c → [ (c + -c) ≡ₚ 0f ] → [ w ≤ (min a b + c) ]
      γ -c p = (
        (w      ≤ (a + c)     ) ⊓ (w      ≤ (b + c)     ) ⇒ᵖ⟨ (λ{ (q , r) → +-creates-≤ w (a + c) -c .fst q , +-creates-≤ w (b + c) -c .fst r}) ⟩
        (w + -c ≤ (a + c) + -c) ⊓ (w + -c ≤ (b + c) + -c) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → w + -c ≤ p) (+-assoc a c -c) q , substₚ (λ p → w + -c ≤ p) (+-assoc b c -c) r}) ⟩
        (w + -c ≤ a + (c + -c)) ⊓ (w + -c ≤ b + (c + -c)) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → w + -c ≤ a + p) p q , substₚ (λ p → w + -c ≤ b + p) p r}) ⟩
        (w + -c ≤ a + 0f      ) ⊓ (w + -c ≤ b + 0f      ) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → w + -c ≤ p) (+-identityʳ a) q , substₚ (λ p → w + -c ≤ p) (+-identityʳ b) r}) ⟩
        (w + -c ≤ a           ) ⊓ (w + -c ≤ b           ) ⇒ᵖ⟨ is-min a b (w + -c) .snd ⟩
        (w + -c       ≤ min a b    )                      ⇒ᵖ⟨ +-creates-≤ (w + -c) (min a b) c .fst ⟩
        ((w + -c) + c ≤ min a b + c)                      ⇒ᵖ⟨ substₚ (λ p → p ≤ min a b + c) (+-assoc w -c c) ⟩
        (w + (-c + c) ≤ min a b + c)                      ⇒ᵖ⟨ substₚ (λ p → w + p ≤ min a b + c) (substₚ (λ p → p ≡ₚ 0f) (+-comm c -c) p) ⟩
        (w + 0f       ≤ min a b + c)                      ⇒ᵖ⟨ substₚ (λ p → p ≤ min a b + c) (+-identityʳ w) ⟩
        (w            ≤ min a b + c)                      ◼ᵖ) .snd (w≤a+c , w≤b+c)

    ≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ]
    ≤-max-+ a b c w a+c≤w b+c≤ = ∣∣-elim (λ _ → isProp[] ((max a b + c) ≤ w)) (λ{ (-c , p) → γ -c p }) (+-inv'' c) where
      γ : ∀ -c → [ (c + -c) ≡ₚ 0f ] → [ (max a b + c) ≤ w ]
      γ -c p = (
        ((a + c)      ≤ w     ) ⊓ ((b + c)      ≤ w     ) ⇒ᵖ⟨ (λ{ (q , r) → +-creates-≤ (a + c) w -c .fst q , +-creates-≤ (b + c) w -c .fst r }) ⟩
        ((a + c) + -c ≤ w + -c) ⊓ ((b + c) + -c ≤ w + -c) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → p ≤ w + -c) (+-assoc a c -c) q , substₚ (λ p → p ≤ w + -c) (+-assoc b c -c) r }) ⟩
        (a + (c + -c) ≤ w + -c) ⊓ (b + (c + -c) ≤ w + -c) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → a + p ≤ w + -c) p q , substₚ (λ p → b + p ≤ w + -c) p r }) ⟩
        (a + 0f       ≤ w + -c) ⊓ (b + 0f       ≤ w + -c) ⇒ᵖ⟨ (λ{ (q , r) → substₚ (λ p → p ≤ w + -c) (+-identityʳ a) q , substₚ (λ p → p ≤ w + -c) (+-identityʳ b) r }) ⟩
        (a            ≤ w + -c) ⊓ (b            ≤ w + -c) ⇒ᵖ⟨ is-max a b (w + -c) .snd ⟩
        (max a b ≤ w + -c)                                ⇒ᵖ⟨ +-creates-≤ (max a b) (w + -c) c .fst ⟩
        (max a b + c ≤ (w + -c)  + c)                     ⇒ᵖ⟨ substₚ (λ p → max a b + c ≤ p) (+-assoc w -c c) ⟩
        (max a b + c ≤ w + (-c + c))                      ⇒ᵖ⟨ substₚ (λ p → max a b + c ≤ w + p) (substₚ (λ p → p ≡ₚ 0f) (+-comm c -c) p) ⟩
        (max a b + c ≤ w + 0f)                            ⇒ᵖ⟨ substₚ (λ p → max a b + c ≤ p) (+-identityʳ w) ⟩
        (max a b + c ≤ w)                                 ◼ᵖ) .snd (a+c≤w , b+c≤)

  module ·-inv⇒
    {ℓ}
    (_·_ : A → A → A)
    (_#_ : hPropRel A A ℓ)
    (0f 1f : A)
    (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
    (·-assoc     : ∀ a b c → [ ((a · b) · c) ≡ₚ (a · (b · c)) ])
    (·-identityʳ : ∀ x → [ (x · 0f) ≡ₚ x ])
    (·-comm      : ∀ a b → [ (a · b) ≡ₚ (b · a) ])
    (·-inv''     : ∀ x → [ ∃[ y ] (x · y) ≡ₚ 1f ])
    where

    -- ≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ]
    -- ≤-min-· a b c w w≤a·c w≤b· = {! is-min a b  !}
    --
    -- ≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ]
    -- ≤-max-· a b c w a·c≤w b·c≤ = {!   !}

  module ≤-dicho⇒+
    (_+_ : A → A → A)
    (≤-dicho : ∀ x y → [ (x ≤ y) ⊔ (y ≤ x) ])
    where

    ≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ]
    ≤-min-+ a b c w w≤a+c w≤b+c = case ≤-dicho a b as (a ≤ b) ⊔ (b ≤ a) ⇒ (w ≤ (min a b + c)) of λ
     { (inl a≤b) → substₚ (λ p → w ≤ p + c) (symₚ (min-identity-≤ a b a≤b)) w≤a+c
     ; (inr b≤a) → substₚ (λ p → w ≤ p + c) (substₚ (λ p → b ≡ₚ p) (min-comm b a) (symₚ (min-identity-≤ b a b≤a))) w≤b+c
     }

    ≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ]
    ≤-max-+ a b c w a+c≤w b+c≤w = case ≤-dicho a b as (a ≤ b) ⊔ (b ≤ a) ⇒ ((max a b + c) ≤ w) of λ
     { (inl a≤b) → substₚ (λ p → p + c ≤ w) (symₚ (max-identity-≤ a b a≤b)) b+c≤w
     ; (inr b≤a) → substₚ (λ p → p + c ≤ w) (substₚ (λ p → a ≡ₚ p) (max-comm b a) (symₚ (max-identity-≤ b a b≤a))) a+c≤w
     }

  module ≤-dicho⇒·
    (_·_ : A → A → A)
    (≤-dicho : ∀ x y → [ (x ≤ y) ⊔ (y ≤ x) ])
    where

    ≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ]
    ≤-min-· a b c w w≤a·c w≤b·c = case ≤-dicho a b as (a ≤ b) ⊔ (b ≤ a) ⇒ (w ≤ (min a b · c)) of λ
     { (inl a≤b) → substₚ (λ p → w ≤ p · c) (symₚ (min-identity-≤ a b a≤b)) w≤a·c
     ; (inr b≤a) → substₚ (λ p → w ≤ p · c) (substₚ (λ p → b ≡ₚ p) (min-comm b a) (symₚ (min-identity-≤ b a b≤a))) w≤b·c
     }

    ≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ]
    ≤-max-· a b c w a·c≤w b·c≤w = case ≤-dicho a b as (a ≤ b) ⊔ (b ≤ a) ⇒ ((max a b · c) ≤ w) of λ
     { (inl a≤b) → substₚ (λ p → p · c ≤ w) (symₚ (max-identity-≤ a b a≤b)) b·c≤w
     ; (inr b≤a) → substₚ (λ p → p · c ≤ w) (substₚ (λ p → a ≡ₚ p) (max-comm b a) (symₚ (max-identity-≤ b a b≤a))) a·c≤w
     }

  +-min-distribʳ' : (_+_ : A → A → A) (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                  → ∀ x y z w → [ (w ≤ (min x y + z)) ⇒ (w ≤ min (x + z) (y + z)) ]
  +-min-distribʳ' _+_ +-creates-≤ x y z w p = (
    ( min x y       ≤  x     ) ⊓ ( min x y      ≤  y     ) ⇒ᵖ⟨ (λ{ (q , r) → +-creates-≤ (min x y) x z .fst q , +-creates-≤ (min x y) y z .fst r}) ⟩
    ((min x y + z ) ≤ (x + z)) ⊓ ((min x y + z) ≤ (y + z)) ⇒ᵖ⟨ (λ{ (q , r) → ≤-trans _ _ _ p q , ≤-trans _ _ _ p r}) ⟩
    ( w             ≤ (x + z)) ⊓ ( w            ≤ (y + z)) ⇒ᵖ⟨ is-min (x + z) (y + z) w .snd ⟩
    ( w ≤ min (x + z) (y + z))                             ◼ᵖ) .snd (min-≤ x y)

  ·-min-distribʳ' : (0f : A) (_·_ : A → A → A) (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                  → ∀ x y z w → [ 0f ≤ z ] → [ (w ≤ (min x y · z)) ⇒ (w ≤ min (x · z) (y · z)) ]
  ·-min-distribʳ' 0f _·_ ·-creates-≤ x y z w 0≤z p = (
    ( min x y      ≤  x     ) ⊓ ( min x y      ≤ y      ) ⇒ᵖ⟨ (λ{ (q , r) → ·-creates-≤ (min x y) x z 0≤z .fst q , ·-creates-≤ (min x y) y z 0≤z .fst r}) ⟩
    ((min x y · z) ≤ (x · z)) ⊓ ((min x y · z) ≤ (y · z)) ⇒ᵖ⟨ (λ{ (q , r) → ≤-trans _ _ _ p q , ≤-trans _ _ _ p r}) ⟩
    ( w            ≤ (x · z)) ⊓ ( w            ≤ (y · z)) ⇒ᵖ⟨ is-min (x · z) (y · z) w .snd ⟩
    ( w ≤ min (x · z) (y · z))                            ◼ᵖ) .snd (min-≤ x y)

  +-max-distribʳ' : (_+_ : A → A → A) (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                  → ∀ x y z w → [ ((max x y + z) ≤ w) ⇒ (max (x + z) (y + z) ≤ w) ]
  +-max-distribʳ' _+_ +-creates-≤ x y z w p = (
    ( x      ≤  max x y      ) ⊓ ( y      ≤  max x y     ) ⇒ᵖ⟨ (λ{ (q , r) → +-creates-≤ x (max x y) z .fst q , +-creates-≤ y (max x y) z .fst r}) ⟩
    ((x + z) ≤ (max x y + z )) ⊓ ((y + z) ≤ (max x y + z)) ⇒ᵖ⟨ (λ{ (q , r) → ≤-trans _ _ _ q p , ≤-trans _ _ _ r p}) ⟩
    ((x + z) ≤  w            ) ⊓ ((y + z) ≤  w           ) ⇒ᵖ⟨ is-max (x + z) (y + z) w .snd ⟩
    ( max (x + z) (y + z) ≤ w)                             ◼ᵖ) .snd (max-≤ x y)

  ·-max-distribʳ' : (0f : A) (_·_ : A → A → A) (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                  → ∀ x y z w → [ 0f ≤ z ] → [ ((max x y · z) ≤ w) ⇒ (max (x · z) (y · z) ≤ w) ]
  ·-max-distribʳ' 0f _·_ ·-creates-≤ x y z w 0≤z p = (
    ( x      ≤  max x y     ) ⊓ (y       ≤  max x y     ) ⇒ᵖ⟨ (λ{ (q , r) → ·-creates-≤ x (max x y) z 0≤z .fst q , ·-creates-≤ y (max x y) z 0≤z .fst r}) ⟩
    ((x · z) ≤ (max x y · z)) ⊓ ((y · z) ≤ (max x y · z)) ⇒ᵖ⟨ (λ{ (q , r) → ≤-trans _ _ _ q p , ≤-trans _ _ _ r p}) ⟩
    ((x · z) ≤  w           ) ⊓ ((y · z) ≤  w           ) ⇒ᵖ⟨ is-max (x · z) (y · z) w .snd ⟩
    ( max (x · z) (y · z) ≤ w)                            ◼ᵖ) .snd (max-≤ x y)

  +-min-distribʳ : (_+_ : A → A → A)
                 → (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                 → (≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ])
                 → ∀ x y z → [ (min x y + z) ≡ₚ min (x + z) (y + z) ]
  +-min-distribʳ _+_ +-creates-≤ ≤-min-+ x y z = ≤-reflectsʳ-≡ (min x y + z) (min (x + z) (y + z)) .fst γ where
    γ : ∀ w → [ (w ≤ (min x y + z)) ⇔ (w ≤ min (x + z) (y + z)) ]
    γ w .fst p = +-min-distribʳ' _+_ +-creates-≤ x y z w p
    γ w .snd p = let (w≤x+z , w≤y+z) = is-min (x + z) (y + z) w .fst p
                 in ≤-min-+ x y z w w≤x+z w≤y+z

  ·-min-distribʳ : (0f : A) (_·_ : A → A → A)
                 → (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                 → (≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ])
                 → ∀ x y z → [ 0f ≤ z ] → [ (min x y · z) ≡ₚ min (x · z) (y · z) ]
  ·-min-distribʳ 0f _·_ ·-creates-≤ ≤-min-· x y z 0≤z = ≤-reflectsʳ-≡ (min x y · z) (min (x · z) (y · z)) .fst γ where
    γ : ∀ w → [ (w ≤ (min x y · z)) ⇔ (w ≤ min (x · z) (y · z)) ]
    γ w .fst p = ·-min-distribʳ' 0f _·_ ·-creates-≤ x y z w 0≤z p
    γ w .snd p = let (w≤x·z , w≤y·z) = is-min (x · z) (y · z) w .fst p
                 in ≤-min-· x y z w w≤x·z w≤y·z

  +-max-distribʳ : (_+_ : A → A → A)
                 → (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                 → (≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ])
                 → ∀ x y z → [ (max x y + z) ≡ₚ max (x + z) (y + z) ]
  +-max-distribʳ _+_ +-creates-≤ ≤-max-+ x y z = ≤-reflectsˡ-≡ (max x y + z) (max (x + z) (y + z)) .fst γ where
    γ : ∀ w → [ ((max x y + z) ≤ w) ⇔ (max (x + z) (y + z) ≤ w) ]
    γ w .fst p = +-max-distribʳ' _+_ +-creates-≤ x y z w p
    γ w .snd p = let (w≤x+z , w≤y+z) = is-max (x + z) (y + z) w .fst p
                 in ≤-max-+ x y z w w≤x+z w≤y+z

  ·-max-distribʳ : (0f : A) (_·_ : A → A → A)
                 → (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                 → (≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ])
                 → ∀ x y z → [ 0f ≤ z ] → [ (max x y · z) ≡ₚ max (x · z) (y · z) ]
  ·-max-distribʳ 0f _·_ ·-creates-≤ ≤-max-· x y z 0≤z = ≤-reflectsˡ-≡ (max x y · z) (max (x · z) (y · z)) .fst γ where
    γ : ∀ w → [ ((max x y · z) ≤ w) ⇔ (max (x · z) (y · z) ≤ w) ]
    γ w .fst p = ·-max-distribʳ' 0f _·_ ·-creates-≤ x y z w 0≤z p
    γ w .snd p = let (w≤x·z , w≤y·z) = is-max (x · z) (y · z) w .fst p
                 in ≤-max-· x y z w w≤x·z w≤y·z

-- -flips-min : ∀ x y → min (- x) (- y) ≡ - max x y
-- -flips-min x y = ?
--
-- -·-flips-min : ∀ x y z → [ z < 0 ] → min x y · z ≡ max (x · z) (y · z)
-- -·-flips-min x y z = ?

module OnSet (is-set : isSet A)
  (let _≡ˢ_ = λ(x y : A) → SyntheticReals.MoreLogic.Definitions.≡ˢ-syntax x y {is-set}
       infixl 4 _≡ˢ_
  ) where

  open OnType public using (min-≤; max-≤)
  module ≤-dicho⇒+ = OnType.≤-dicho⇒+
  module ≤-dicho⇒· = OnType.≤-dicho⇒·

  ≤-reflectsʳ-≡ : ∀ x y → [ (∀[ z ] z ≤ x ⇔ z ≤ y) ⇔ x ≡ˢ y ]
  ≤-reflectsʳ-≡ x y .fst p = ∣∣-elim (λ c → is-set x y) (λ x → x) (OnType.≤-reflectsʳ-≡ x y .fst p)
  ≤-reflectsʳ-≡ x y .snd p = OnType.≤-reflectsʳ-≡ x y .snd ∣ p ∣

  ≤-reflectsˡ-≡ : ∀ x y → [ (∀[ z ] x ≤ z ⇔ y ≤ z) ⇔ x ≡ˢ y ]
  ≤-reflectsˡ-≡ x y .fst p = ∣∣-elim (λ c → is-set x y) (λ x → x) (OnType.≤-reflectsˡ-≡ x y .fst p)
  ≤-reflectsˡ-≡ x y .snd p = OnType.≤-reflectsˡ-≡ x y .snd ∣ p ∣

  min-identity : ∀ x → [ min x x ≡ˢ x ]
  min-identity x = ∣∣-elim (λ c → is-set (min x x) x) (λ x → x) (OnType.min-identity x)

  min-identity-≤ : ∀ x y → [ x ≤ y ] → [ min x y ≡ˢ x ]
  min-identity-≤ x y p = ∣∣-elim (λ c → is-set (min x y) x) (λ x → x) (OnType.min-identity-≤ x y p)

  max-identity-≤ : ∀ x y → [ x ≤ y ] → [ max x y ≡ˢ y ]
  max-identity-≤ x y p = ∣∣-elim (λ c → is-set (max x y) y) (λ x → x) (OnType.max-identity-≤ x y p)

  min-comm : ∀ x y → [ min x y ≡ˢ min y x ]
  min-comm x y = ∣∣-elim (λ c → is-set (min x y) (min y x)) (λ x → x) (OnType.min-comm x y)

  min-assoc : ∀ x y z → [ min (min x y) z ≡ˢ min x (min y z) ]
  min-assoc x y z = ∣∣-elim (λ c → is-set (min (min x y) z) (min x (min y z))) (λ x → x) (OnType.min-assoc x y z)

  max-identity : ∀ x → [ max x x ≡ˢ x ]
  max-identity x = ∣∣-elim (λ c → is-set (max x x) x) (λ x → x) (OnType.max-identity x)

  max-comm : ∀ x y → [ max x y ≡ˢ max y x ]
  max-comm x y = ∣∣-elim (λ c → is-set (max x y) (max y x)) (λ x → x) (OnType.max-comm x y)

  max-assoc : ∀ x y z → [ max (max x y) z ≡ˢ max x (max y z) ]
  max-assoc x y z = ∣∣-elim (λ c → is-set (max (max x y) z) (max x (max y z))) (λ x → x) (OnType.max-assoc x y z)

  min-max-absorptive : ∀ x y → [ min x (max x y) ≡ˢ x ]
  min-max-absorptive x y = ∣∣-elim (λ c → is-set (min x (max x y)) x) (λ x → x) (OnType.min-max-absorptive x y)

  max-min-absorptive : ∀ x y → [ max x (min x y) ≡ˢ x ]
  max-min-absorptive x y = ∣∣-elim (λ c → is-set (max x (min x y)) x) (λ x → x) (OnType.max-min-absorptive x y)

  +-min-distribʳ : (_+_ : A → A → A)
                 → (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                 → (≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ])
                 → ∀ x y z → [ (min x y + z) ≡ˢ min (x + z) (y + z) ]
  +-min-distribʳ _+_ +-creates-≤ ≤-min-+ x y z = ∣∣-elim (λ c → is-set (min x y + z) (min (x + z) (y + z))) (λ x → x) (OnType.+-min-distribʳ _+_ +-creates-≤ ≤-min-+ x y z)

  ·-min-distribʳ : (0f : A) (_·_ : A → A → A)
                 → (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                 → (≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ])
                 → ∀ x y z → [ 0f ≤ z ] → [ (min x y · z) ≡ˢ min (x · z) (y · z) ]
  ·-min-distribʳ 0f _·_ ·-creates-≤ ≤-min-· x y z 0≤z = ∣∣-elim (λ c → is-set (min x y · z) (min (x · z) (y · z))) (λ x → x) (OnType.·-min-distribʳ 0f _·_ ·-creates-≤ ≤-min-· x y z 0≤z)

  +-max-distribʳ : (_+_ : A → A → A)
                 → (+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ])
                 → (≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ])
                 → ∀ x y z → [ (max x y + z) ≡ˢ max (x + z) (y + z) ]
  +-max-distribʳ _+_ +-creates-≤ ≤-max-+ x y z = ∣∣-elim (λ c → is-set (max x y + z) (max (x + z) (y + z))) (λ x → x) (OnType.+-max-distribʳ _+_ +-creates-≤ ≤-max-+ x y z)

  ·-max-distribʳ : (0f : A) (_·_ : A → A → A)
                 → (·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ])
                 → (≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ])
                 → ∀ x y z → [ 0f ≤ z ] → [ (max x y · z) ≡ˢ max (x · z) (y · z) ]
  ·-max-distribʳ 0f _·_ ·-creates-≤ ≤-max-· x y z 0≤z = ∣∣-elim (λ c → is-set (max x y · z) (max (x · z) (y · z))) (λ x → x) (OnType.·-max-distribʳ 0f _·_ ·-creates-≤ ≤-max-· x y z 0≤z)
