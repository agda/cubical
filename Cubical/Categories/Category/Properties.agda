{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category.Base

open Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where

  -- isSet where your allowed to compare paths where one side is only
  -- equal up to path. Is there a generalization of this?
  isSetHomP1 : ∀ {x y : C .ob} {n : C [ x , y ]}
              → isOfHLevelDep 1 (λ m → m ≡ n)
  isSetHomP1 {x = x} {y} {n} = isOfHLevel→isOfHLevelDep 1 (λ m → isSetHom C m n)

  -- isSet where the arrows can be between non-definitionally equal obs
  isSetHomP2l : ∀ {y : C .ob}
              → isOfHLevelDep 2 (λ x → C [ x , y ])
  isSetHomP2l = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom C {x = a})

  isSetHomP2r : ∀ {x : C .ob}
              → isOfHLevelDep 2 (λ y → C [ x , y ])
  isSetHomP2r = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom C {y = a})


-- opposite of opposite is definitionally equal to itself
involutiveOp : ∀ {C : Category ℓ ℓ'} → C ^op ^op ≡ C
involutiveOp = refl

module _ {C : Category ℓ ℓ'} where
  -- Other useful operations on categories

  -- whisker the parallel morphisms g and g' with f
  lCatWhisker : {x y z : C .ob} (f : C [ x , y ]) (g g' : C [ y , z ]) (p : g ≡ g')
                 → f ⋆⟨ C ⟩ g ≡ f ⋆⟨ C ⟩ g'
  lCatWhisker f _ _ p = cong (_⋆_ C f) p

  rCatWhisker : {x y z : C .ob} (f f' : C [ x , y ]) (g : C [ y , z ]) (p : f ≡ f')
                 → f ⋆⟨ C ⟩ g ≡ f' ⋆⟨ C ⟩ g
  rCatWhisker _ _ g p = cong (λ v → v ⋆⟨ C ⟩ g) p

  -- working with equal objects
  idP : ∀ {x x'} {p : x ≡ x'} → C [ x , x' ]
  idP {x} {x'} {p} = subst (λ v → C [ x , v ]) p (C .id)

  -- heterogeneous seq
  seqP : ∀ {x y y' z} {p : y ≡ y'}
       → (f : C [ x , y ]) (g : C [ y' , z ])
       → C [ x , z ]
  seqP {x} {_} {_} {z} {p} f g = f ⋆⟨ C ⟩ (subst (λ a → C [ a , z ]) (sym p) g)

  -- also heterogeneous seq, but substituting on the left
  seqP' : ∀ {x y y' z} {p : y ≡ y'}
        → (f : C [ x , y ]) (g : C [ y' , z ])
        → C [ x , z ]
  seqP' {x} {_} {_} {z} {p} f g = subst (λ a → C [ x , a ]) p f ⋆⟨ C ⟩ g

  -- show that they're equal
  seqP≡seqP' : ∀ {x y y' z} {p : y ≡ y'}
             → (f : C [ x , y ]) (g : C [ y' , z ])
             → seqP {p = p} f g ≡ seqP' {p = p} f g
  seqP≡seqP' {x = x} {z = z} {p = p} f g i =
    (toPathP {A = λ i' → C [ x , p i' ]} {f} refl i)
      ⋆⟨ C ⟩
    (toPathP {A = λ i' → C [ p (~ i') , z ]} {x = g} (sym refl) (~ i))

  -- seqP is equal to normal seq when y ≡ y'
  seqP≡seq : ∀ {x y z}
           → (f : C [ x , y ]) (g : C [ y , z ])
           → seqP {p = refl} f g ≡ f ⋆⟨ C ⟩ g
  seqP≡seq {y = y} {z} f g i = f ⋆⟨ C ⟩ toPathP {A = λ _ → C [ y , z ]} {x = g} refl (~ i)


  -- whiskering with heterogenous seq -- (maybe should let z be heterogeneous too)
  lCatWhiskerP : {x y z y' : C .ob} {p : y ≡ y'}
                  → (f : C [ x , y ]) (g : C [ y , z ]) (g' : C [ y' , z ])
                  → (r : PathP (λ i → C [ p i , z ]) g g')
                  → f ⋆⟨ C ⟩ g ≡ seqP {p = p} f g'
  lCatWhiskerP {z = z} {p = p} f g g' r =
    cong (λ v → f ⋆⟨ C ⟩ v) (sym (fromPathP (symP {A = λ i → C [ p (~ i) , z ]} r)))

  rCatWhiskerP : {x y' y z : C .ob} {p : y' ≡ y}
                  → (f' : C [ x , y' ]) (f : C [ x , y ]) (g : C [ y , z ])
                  → (r : PathP (λ i → C [ x , p i ]) f' f)
                  → f ⋆⟨ C ⟩ g ≡ seqP' {p = p} f' g
  rCatWhiskerP f' f g r = cong (λ v → v ⋆⟨ C ⟩ g) (sym (fromPathP r))
