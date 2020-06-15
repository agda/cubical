{-

The purpose of this module is to provide the way of
turning functions from nested Sigma Types into functions of multiple arguments

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Currying where


open import Cubical.Data.Nat

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything


open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested


-- isomorphism between explicit and implicit dependent functions


Π : ∀ {ℓ ℓ'} → {A : Type ℓ} → (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π B = ∀ x → B x

Π' : ∀ {ℓ ℓ'} → {A : Type ℓ} → (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π' B = ∀ {x} → B x

iso-Π-Π' : ∀ {ℓ ℓ'} {A : Type ℓ}
               → (B : A → Type ℓ')
               → Iso (Π B) (Π' B)
iso-Π-Π' B = iso (λ x {y} → x y) (λ x y → x {y}) (λ b → refl) (λ b → refl)

-- function space of "configurable" explicity

Π-u : ∀ {ℓ ℓ'} {A : Type ℓ}
               → Bool
               → (B : A → Type ℓ')
               → Type (ℓ-max ℓ ℓ')
Π-u = caseBool Π' Π


iso-Π-u : ∀ {ℓ ℓ'} {A : Type ℓ}
               → (B : A → Type ℓ')
               → ∀ b₁ b₂
               → Iso (Π-u b₁ B) (Π-u b₂  B)
iso-Π-u B false false = idIso
iso-Π-u B false true = iso-Π-Π' B
iso-Π-u B true false = invIso (iso-Π-Π' B)
iso-Π-u B true true = idIso


-- helper for defining functions of "configurable" explicity
λ-u : ∀ {ℓ ℓ'} {A : Type ℓ} → {B : A → Type ℓ'}
               → ∀ b → Π B → Π-u b B
λ-u {B = B} false f = f
λ-u {B = B} true f {x} = f x


-- helper for applying function of "configurable" explicity
app-u : ∀ {ℓ ℓ'} {A : Type ℓ}
               → {B : A → Type ℓ'}
               → ∀ b → Π-u b B  → Π B
app-u false x = x
app-u true x x₁ = x {x₁}

λ-u= : ∀ {ℓ ℓ'} {A : Type ℓ}
               → {B : A → Type ℓ'} → ∀ b
               → ∀ f → λ-u b (app-u {A = A} {B = B} b f) ≡ f
λ-u= false f = refl
λ-u= true f = refl

app-u= : ∀ {ℓ ℓ'} {A : Type ℓ}
               → {B : A → Type ℓ'} → ∀ b
               → ∀ f → app-u b (λ-u {A = A} {B = B} b f) ≡ f
app-u= false f = refl
app-u= true f = refl

-- n-curriedᵣ-conf function, for Type family parametrised by nested sigma
-- produce type of related curried functions
-- this is used to write the signature of n-curry and n-uncurry functions

-- "-conf" postfix marks "configurable" versions, where explicity of each
-- argument can be provided


n-curriedᵣ-conf : ∀ {ℓ ℓ'} → ∀ {n} → Vec Bool n → (s : Sig ℓ n)
                     → (NestedΣᵣ s → Type ℓ') → Type (ℓ-max ℓ ℓ')
n-curriedᵣ-conf {ℓ} {n = zero} v s Target = Lift {_} {ℓ} (Target _)
n-curriedᵣ-conf {n = suc zero} v s = Π-u (head v)
n-curriedᵣ-conf {n = suc (suc n)} v s Target =
  Π-u (head v) λ x → n-curriedᵣ-conf (tail v) (snd s x) (Target ∘ (x ,_))

n-curryᵣ-conf : ∀ {ℓ ℓ'} → ∀ {n} → (v : Vec Bool n) → (s : Sig ℓ n)
                     → {Target : NestedΣᵣ s → Type ℓ'}
                     → Π Target → n-curriedᵣ-conf v s Target
n-curryᵣ-conf {n = zero} v s x = lift (x _)
n-curryᵣ-conf {n = suc zero} v s = λ-u (head v)
n-curryᵣ-conf {n = suc (suc n)} v s f =
  λ-u (head v) λ x → n-curryᵣ-conf (tail v) (snd s x) (f ∘ (x ,_))

n-uncurryᵣ-conf : ∀ {ℓ ℓ'} → ∀ {n} → (v : Vec Bool n) → (s : Sig ℓ n)
                  → {Target : NestedΣᵣ s → Type ℓ'}
                  → n-curriedᵣ-conf v s Target → Π Target
n-uncurryᵣ-conf {n = zero} v s x _ = lower x
n-uncurryᵣ-conf {n = suc zero} v s x = app-u (head v) x
n-uncurryᵣ-conf {n = suc (suc n)} v s x (a , y) =
  n-uncurryᵣ-conf (tail v) (snd s a) ( app-u (head v) x a) y

n-curryᵣ-uncurryᵣ-conf-Iso : ∀ {ℓ ℓ'} → ∀ {n} → (v : Vec Bool n) → (s : Sig ℓ n)
                  → {Target : NestedΣᵣ s → Type ℓ'}
                  → Iso (Π Target) (n-curriedᵣ-conf v s Target)
Iso.fun (n-curryᵣ-uncurryᵣ-conf-Iso v s) = n-curryᵣ-conf v s
Iso.inv (n-curryᵣ-uncurryᵣ-conf-Iso v s) = n-uncurryᵣ-conf v s
Iso.rightInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = zero} v s) b = refl
Iso.rightInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = suc zero} v s) = λ-u= (head v)
Iso.rightInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = suc (suc n)} v s) b =
  cong (λ-u (head v)) (funExt (λ x →
          Iso.rightInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = suc n} (tail v) (snd s x))
                              (app-u (head v) b x))) ∙ λ-u= (head v) b
Iso.leftInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = zero} v s) a = refl
Iso.leftInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = suc zero} v s) = app-u= (head v)
Iso.leftInv (n-curryᵣ-uncurryᵣ-conf-Iso {n = suc (suc n)} v s) a =
  let f' = (λ x₁ → n-curryᵣ-conf _ (snd s x₁) (λ x₂ → a (x₁ , x₂)))
  in
  funExt
    (uncurry λ x → funExt⁻
       ( cong (n-uncurryᵣ-conf (tail v) _) (cong (λ f → f x) (app-u= (head v) f'))
         ∙ (Iso.leftInv (n-curryᵣ-uncurryᵣ-conf-Iso (tail v) (snd s x)) (a ∘ (x ,_)))))

----------


-- preconfigured versions of above functions, for all explicit arguments

n-curriedᵣ : ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                     → ((NestedΣᵣ s → Type ℓ')) → Type (ℓ-max ℓ ℓ')
n-curriedᵣ = n-curriedᵣ-conf (repeat false)


n-curryᵣ :  ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                     → {Target : NestedΣᵣ s → Type ℓ'}
                     → Π Target → n-curriedᵣ-conf (repeat false) s Target
n-curryᵣ = n-curryᵣ-conf (repeat false)

n-uncurryᵣ :  ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                     → {Target : NestedΣᵣ s → Type ℓ'}
                     → n-curriedᵣ-conf (repeat false) s Target → Π Target
n-uncurryᵣ = n-uncurryᵣ-conf (repeat false)

n-curryᵣ-uncurryᵣ-Iso : ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                  → {Target : NestedΣᵣ s → Type ℓ'}
                  → Iso (Π Target) (n-curriedᵣ s Target)
n-curryᵣ-uncurryᵣ-Iso = n-curryᵣ-uncurryᵣ-conf-Iso (repeat false)

-- and all implicit arguments


n-curriedᵣ-implicit :  ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                     → ((NestedΣᵣ s → Type ℓ')) → Type (ℓ-max ℓ ℓ')
n-curriedᵣ-implicit = n-curriedᵣ-conf (repeat false)

n-curryᵣ-implicit :  ∀ {ℓ ℓ'} → ∀ {n} → (s : Sig ℓ n)
                     → {Target : NestedΣᵣ s → Type ℓ'}
                     → Π Target → n-curriedᵣ-conf (repeat true) s Target
n-curryᵣ-implicit = n-curryᵣ-conf (repeat true)

----------

-- this signature is given for any n

Sig-of-Sig : ∀ {ℓ} → ∀ n → Sig (ℓ-suc ℓ) n


-- NestedΣᵣ coresponding to this signature is equivalent to Sig of previous Level
-- together with functions to manipulate NestedΣ, this Signature helps to introduce
-- multiple dependent families into context

NestedΣᵣ-≃-Sig : ∀ {ℓ} → ∀ {n}
                    → (NestedΣᵣ (Sig-of-Sig {ℓ} n)) ≃ (Sig ℓ n)

Sig-of-Sig zero = _
Sig-of-Sig (suc zero) = Type _
Sig-of-Sig (suc (suc n)) =
  sig-n+1.from (suc n)
    (Sig-of-Sig (suc n) ,
      (λ x → n-curriedᵣ {n = suc n} x (const (Type _))  ) ∘ (equivFun NestedΣᵣ-≃-Sig))

NestedΣᵣ-≃-Sig {n = zero} = idEquiv _
NestedΣᵣ-≃-Sig {n = suc zero} = idEquiv _
NestedΣᵣ-≃-Sig {n = suc (suc zero)} = idEquiv _
NestedΣᵣ-≃-Sig {n = suc (suc (suc n))} =
 let
     nestedΣ-unsplit = nestedΣᵣ-n+1.isom-from _ (Sig-of-Sig (suc (suc n)) ,
                         (λ x → n-curriedᵣ {n = suc (suc n)} x _ ) ∘ _)

     curr-uncurr x = invEquiv
                       (isoToEquiv (n-curryᵣ-uncurryᵣ-Iso {n = suc (suc n)}_ ))

 in
    _ ≃⟨ isoToEquiv nestedΣ-unsplit ⟩
    _ ≃⟨ Σ-cong-equiv-fst NestedΣᵣ-≃-Sig ⟩
    _ ≃⟨ Σ-cong-equiv-snd curr-uncurr ⟩
    _ ≃⟨ isoToEquiv (sig-n+1.isom _) ⟩ _ ■


-- this function generates analogue of Σ-assoc-≃ "all the way down"

Σ-par-assoc-n : ∀ {ℓ} → (p : Par)
              → _
Σ-par-assoc-n {ℓ} p = n-curryᵣ (Sig-of-Sig {ℓ} (len p))
                   (isoToEquiv ∘ NestedΣ-NestedΣᵣ-Iso p ∘ (equivFun NestedΣᵣ-≃-Sig))


--- this function helps to create descriptions of explicity of arguments
--- consecutive numbers mark lengh of strings of explicit and implicit arguments
--- from argument (2 ∷ 3 ∷ 1 ∷ []) it generates
--  (repeat {2} false ++ repeat {3} true  ++ repeat {1} false)


impex' :  Bool → List ℕ → Σ _ (Vec Bool)
impex' x [] = _ , []
impex' x (zero ∷ x₂) = impex' (not x) x₂
impex' x (suc x₁ ∷ x₂) = _ , (x ∷ snd (impex' x (x₁ ∷ x₂)))

impex : (l : List ℕ) → Vec Bool _
impex = snd ∘ impex' false

-- force casting vectors to diferent length (trimming or padding with false)

castImpex : ∀ {n₁ n₂} → Vec Bool n₁ → Vec Bool n₂
castImpex {zero} _ = repeat false
castImpex {suc n₁} {zero} _ = []
castImpex {suc n₁} {suc n₂} x = head x ∷ castImpex (tail x)

-- helper for extracting signature of function as nested sigma


extractSig : ∀ {ℓ ℓ'}
                   → (l : List ℕ)
                   → {s : Sig ℓ _}
                   → ∀ {r}
                   → (n-curriedᵣ-conf {ℓ' = ℓ'} (impex l) s r)
                   → Sig ℓ _
extractSig l {s} x = s


-- equivalence of functions of different explicity

n-exp-imp-≃ : ∀ {ℓ ℓ'} → ∀ {n}
                   → (v₁ v₂ : Vec Bool n)
                   → (s : Sig ℓ n)
                   → ∀ {r}
                   →  (n-curriedᵣ-conf {ℓ' = ℓ'} v₁ s r)
                    ≃ (n-curriedᵣ-conf {ℓ' = ℓ'} v₂ s r)
n-exp-imp-≃ {n = 0} v₁ v₂ s = idEquiv _
n-exp-imp-≃ {n = 1} v₁ v₂ s = isoToEquiv (iso-Π-u _ (head v₁) (head v₂) )
n-exp-imp-≃ {n = (suc (suc n))} v₁ v₂ s =
    _ ≃⟨ isoToEquiv (iso-Π-u _ (head v₁) false) ⟩
    _ ≃⟨ (equivPi λ x → n-exp-imp-≃ (tail v₁) (tail v₂) (snd s x) ) ⟩
    _ ≃⟨ isoToEquiv (iso-Π-u _ false (head v₂)) ⟩ _ ■


-- given some Sig ℓ n, we can generate type family in following way:
--
-- if signature have length 0, then resulting type family is degenerated into
-- Lift Unit, (wich can be looked at, as  type family without arguments)
--
-- if length of the signature is > 0, then
-- with sig-n+1 we can turn Sig ℓ (suc n) into Σ[ s ∈ Sig ℓ n ] (NestegΣᵣ s → Type ℓ)
--     and then we can curry (NestegΣᵣ s → Type ℓ)

--this function would be simplier if it was defined only for n>0 , but i noticed,
-- that it is usefull to being able to use this function for signatures even if their
-- length is not of the form (suc _)

toTypeFamTy : ∀ {ℓ} → ∀ {n} → (v : Vec Bool (predℕ n)) → Sig ℓ n → Type (ℓ-suc ℓ)
toTypeFamTy {n = zero} _ _ = Type _
toTypeFamTy {n = suc n} v s = n-curriedᵣ-conf v (fst (sig-n+1.to n s)) (λ _ → Type _)

toTypeFam : ∀ {ℓ} → ∀ {n} → (v : Vec Bool (predℕ n)) → (s : Sig ℓ n)
               → toTypeFamTy v s
toTypeFam {n = zero} v s = Lift Unit
toTypeFam {n = suc n} v s = n-curryᵣ-conf v _ (snd (sig-n+1.to _ s))
