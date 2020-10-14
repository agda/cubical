{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.MoreLogic.Reasoning where -- hProp logic

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)

-- "implicational" reaoning

-- infix  3 _◼ᵖ
-- infixr 2 _⇒ᵖ⟨_⟩_
--
-- _⇒ᵖ⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : hProp ℓ'} {R : hProp ℓ''} → (P : hProp ℓ) → [ P ⇒ Q ] → [ Q ⇒ R ] → [ P ⇒ R ]
-- _ ⇒ᵖ⟨ pq ⟩ qr = qr ∘ pq
--
-- _◼ᵖ : ∀{ℓ} (A : hProp ℓ) → [ A ] → [ A ]
-- _ ◼ᵖ = λ x → x

infix  3 _◼
infixr 2 _⇒⟨_⟩_

infix  3 _◼ᵖ
infixr 2 ⇒ᵖ⟨⟩-syntax -- _⇒ᵖ⟨_⟩_

infix  3 _∎ᵖ
infixr 2 ⇔⟨⟩-syntax -- _⇔⟨_⟩_

⇔⟨⟩-syntax : ∀{ℓ ℓ' ℓ''} → (P : hProp ℓ'') → (((Q , R) , _) : Σ[ (Q , R) ∈ hProp ℓ' × hProp ℓ ] [ Q ⇔ R ]) → [ P ⇔ Q ] → Σ[ (P , R) ∈ hProp ℓ'' × hProp ℓ ] [ P ⇔ R ]
⇔⟨⟩-syntax P ((Q , R) , q⇔r) p⇔q .fst = P , R -- x⇔y ∙ y⇔z
⇔⟨⟩-syntax P ((Q , R) , q⇔r) p⇔q .snd .fst = fst q⇔r ∘ fst p⇔q
⇔⟨⟩-syntax P ((Q , R) , q⇔r) p⇔q .snd .snd = snd p⇔q ∘ snd q⇔r

syntax ⇔⟨⟩-syntax P QRq⇔r p⇔q = P ⇔⟨ p⇔q ⟩ QRq⇔r

_∎ᵖ : ∀{ℓ} → (P : hProp ℓ) → Σ[ (Q , R) ∈ hProp ℓ × hProp ℓ ] [ Q ⇔ R ]
_∎ᵖ P .fst        = P , P
_∎ᵖ P .snd .fst x = x
_∎ᵖ P .snd .snd x = x

⇒ᵖ⟨⟩-syntax : ∀{ℓ ℓ' ℓ''} → (P : hProp ℓ'') → (((Q , R) , _) : Σ[ (Q , R) ∈ hProp ℓ' × hProp ℓ ] [ Q ⇒ R ]) → [ P ⇒ Q ] → Σ[ (P , R) ∈ hProp ℓ'' × hProp ℓ ] [ P ⇒ R ]
⇒ᵖ⟨⟩-syntax P ((Q , R) , q⇔r) p⇔q .fst = P , R -- x⇔y ∙ y⇔z
⇒ᵖ⟨⟩-syntax P ((Q , R) , q⇒r) p⇒q .snd = q⇒r ∘ p⇒q

_◼ᵖ : ∀{ℓ} → (P : hProp ℓ) → Σ[ (Q , R) ∈ hProp ℓ × hProp ℓ ] [ Q ⇒ R ]
_◼ᵖ P .fst   = P , P
_◼ᵖ P .snd x = x

syntax ⇒ᵖ⟨⟩-syntax P QRq⇒r p⇒q = P ⇒ᵖ⟨ p⇒q ⟩ QRq⇒r

_⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
_ ⇒⟨ p⇒q ⟩ q⇒r = q⇒r ∘ p⇒q

_◼ : ∀{ℓ} (A : Type ℓ) → A → A
_ ◼ = λ x → x

-- ⊎⇒⊔ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ P ] ⊎ [ Q ] → [ P ⊔ Q ]
-- ⊎⇒⊔ P Q (inl x) = inlᵖ x
-- ⊎⇒⊔ P Q (inr x) = inrᵖ x
--
-- case[_⊔_]_return_of_ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
--                   → (z : [ P ⊔ Q ])
--                   → (R : [ P ⊔ Q ] → hProp ℓ'')
--                   → (S : (x : [ P ] ⊎ [ Q ]) → [ R (⊎⇒⊔ P Q x) ] )
--                   → [ R z ]
-- case[_⊔_]_return_of_ P Q z R S = ⊔-elim P Q R (λ p → S (inl p)) (λ q → S (inr q)) z


{- NOTE: in the CHANGELOG.md of the v1.3 non-cubical standard library, it is explained:

* Previously all equational reasoning combinators (e.g. `_≈⟨_⟩_`, `_≡⟨_⟩_`, `_≤⟨_⟩_`)
  were defined in the following style:
  ```agda
  infixr 2 _≡⟨_⟩_

  _≡⟨_⟩_ : ∀ x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z
  ```
  The type checker therefore infers the RHS of the equational step from the LHS + the
  type of the proof. For example for `x ≈⟨ x≈y ⟩ y ∎` it is inferred that `y ∎`
  must have type `y IsRelatedTo y` from `x : A` and `x≈y : x ≈ y`.

* There are two problems with this. Firstly, it means that the reasoning combinators are
  not compatible with macros (i.e. tactics) that attempt to automatically generate proofs
  for `x≈y`. This is because the reflection machinary does not have access to the type of RHS
  as it cannot be inferred. In practice this meant that the new reflective solvers
  `Tactic.RingSolver` and `Tactic.MonoidSolver` could not be used inside the equational
  reasoning. Secondly the inference procedure itself is slower as described in this
  [exchange](https://lists.chalmers.se/pipermail/agda/2016/009090.html)
  on the Agda mailing list.

* Therefore, as suggested on the mailing list, the order of arguments to the combinators
  have been reversed so that instead the type of the proof is inferred from the LHS + RHS.
  ```agda
  infixr -2 step-≡

  step-≡ : ∀ x {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ y≡z x≡y = trans x≡y y≡z

  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
  ```
  where the `syntax` declaration is then used to recover the original order of the arguments.
  This change enables the use of macros and anecdotally speeds up type checking by a
  factor of 5.

-} -- TODO: that might be "correct" the way to implement these reasoning operators
