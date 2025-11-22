module Cubical.Categories.Dagger.Instances.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Morphism

open import Cubical.Categories.Dagger.Base
open import Cubical.Categories.Dagger.Properties
open import Cubical.Categories.Dagger.Functor

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

open DaggerStr
open IsDagger
open †Category

BinProdDaggerStr : {C : Category ℓ ℓ'} {D : Category ℓ'' ℓ'''} → DaggerStr C → DaggerStr D → DaggerStr (C ×C D)
BinProdDaggerStr dagC dagD ._† (f , g) = dagC ._† f , dagD ._† g
BinProdDaggerStr dagC dagD .is-dag .†-invol (f , g) = ≡-× (dagC .†-invol f) (dagD .†-invol g)
BinProdDaggerStr dagC dagD .is-dag .†-id = ≡-× (dagC .†-id) (dagD .†-id)
BinProdDaggerStr dagC dagD .is-dag .†-seq (f , g) (f' , g') = ≡-× (dagC .†-seq f f') (dagD .†-seq g g')

†BinProd _×†_ : †Category ℓ ℓ' → †Category ℓ'' ℓ''' → †Category (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')
†BinProd C D .cat = C .cat ×C D .cat
†BinProd C D .dagstr = BinProdDaggerStr (C .dagstr) (D .dagstr)
_×†_ = †BinProd

module _ (C : †Category ℓ ℓ') (D : †Category ℓ'' ℓ''') where
  †Fst : †Functor (C ×† D) C
  †Fst .fst = Fst (C .cat) (D .cat)
  †Fst .snd .F-† (f , g) = refl

  †Snd : †Functor (C ×† D) D
  †Snd .fst = Snd (C .cat) (D .cat)
  †Snd .snd .F-† (f , g) = refl

module _ where
  private variable
    B C D E : †Category ℓ ℓ'

  _,†F_ : †Functor C D → †Functor C E → †Functor C (D ×† E)
  (F ,†F G) .fst = F .fst ,F G .fst
  (F ,†F G) .snd .F-† f = ≡-× (F .snd .F-† f) (G .snd .F-† f)

  _×†F_ : †Functor B D → †Functor C E → †Functor (B ×† C) (D ×† E)
  _×†F_ {B = B} {C = C} F G = (F ∘†F †Fst B C) ,†F (G ∘†F †Snd B C)

  †Δ : †Functor C (C ×† C)
  †Δ = †Id ,†F †Id

module _ (C : †Category ℓ ℓ') (D : †Category ℓ'' ℓ''') where
  †Swap : †Functor (C ×† D) (D ×† C)
  †Swap = †Snd C D ,†F †Fst C D

  †Linj : ob D → †Functor C (C ×† D)
  †Linj d = †Id ,†F †Constant d

  †Rinj : ob C → †Functor D (C ×† D)
  †Rinj c = †Constant c ,†F †Id

  open areInv
  open †Morphisms

  †CatIso× : ∀ {x y z w} → †CatIso C x y → †CatIso D z w → †CatIso (C ×† D) (x , z) (y , w)
  †CatIso× (f , fiso) (g , giso) .fst = f , g
  †CatIso× (f , fiso) (g , giso) .snd .sec = ≡-× (fiso .sec) (giso .sec)
  †CatIso× (f , fiso) (g , giso) .snd .ret = ≡-× (fiso .ret) (giso .ret)
