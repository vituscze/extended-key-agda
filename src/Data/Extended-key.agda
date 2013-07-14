open import Relation.Binary

module Data.Extended-key
  {k ℓ₁ ℓ₂}
  {Key : Set k}
  {_≈_ : Rel Key ℓ₁}
  {_<_ : Rel Key ℓ₂}
  (isStrictTotalOrder′ : IsStrictTotalOrder _≈_ _<_)
  where

open import Data.Empty
open import Data.Product
open import Data.Unit
open import Level

infix 4 _≈⁺_
infix 4 _<⁺_
infix 4 _<_<_

data Key⁺ : Set k where
  ⊥⁺ ⊤⁺ :             Key⁺
  [_]   : (k : Key) → Key⁺


_≈⁺_ : Rel Key⁺ ℓ₁
⊥⁺    ≈⁺ ⊥⁺    = Lift ⊤
⊤⁺    ≈⁺ ⊤⁺    = Lift ⊤

[ x ] ≈⁺ [ y ] = x ≈ y

_     ≈⁺ _     = Lift ⊥


_<⁺_ : Rel Key⁺ ℓ₂
⊥⁺    <⁺ [ _ ] = Lift ⊤
⊥⁺    <⁺ ⊤⁺    = Lift ⊤
[ _ ] <⁺ ⊤⁺    = Lift ⊤

[ x ] <⁺ [ y ] = x < y

_     <⁺ _     = Lift ⊥


_<_<_ : Key⁺ → Key → Key⁺ → Set _
x < y < z = x <⁺ [ y ] × [ y ] <⁺ z


⊥⁺-min : ∀ x → ⊥⁺ <⁺ [ x ]
⊥⁺-min _ = _


⊤⁺-max : ∀ x → [ x ] <⁺ ⊤⁺
⊤⁺-max _ = _


isStrictTotalOrder : IsStrictTotalOrder _≈⁺_ _<⁺_
isStrictTotalOrder = record
  { isEquivalence = record
      { refl  = λ
          { {⊥⁺}    → _
          ; {[ x ]} → EQ.refl {x}
          ; {⊤⁺}    → _
          }
      ; sym   = λ {x y} → sym≈ x y
      ; trans = λ {x y z} → trans≈ x y z
      }
  ; trans    = λ {x y z} → trans x y z
  ; compare  = compare
  ; <-resp-≈ = (λ {x y z} → respʳ x y z) , (λ {x y z} → respˡ x y z)
  }
  where
  module TO = IsStrictTotalOrder isStrictTotalOrder′
  module EQ = IsEquivalence TO.isEquivalence

  sym≈ : ∀ x y → x ≈⁺ y → y ≈⁺ x
  sym≈ [ _ ] [ _ ] p = EQ.sym p

  sym≈ ⊥⁺    ⊥⁺    _ = _
  sym≈ ⊤⁺    ⊤⁺    _ = _

  sym≈ ⊥⁺    [ _ ] (lift ())
  sym≈ ⊥⁺    ⊤⁺    (lift ())
  sym≈ [ _ ] ⊥⁺    (lift ())
  sym≈ [ _ ] ⊤⁺    (lift ())
  sym≈ ⊤⁺    ⊥⁺    (lift ())
  sym≈ ⊤⁺    [ _ ] (lift ())


  trans≈ : ∀ x y z → x ≈⁺ y → y ≈⁺ z → x ≈⁺ z
  trans≈ [ _ ] [ _ ] [ _ ] p q = EQ.trans p q

  trans≈ ⊥⁺    ⊥⁺    _     _ q = q
  trans≈ ⊤⁺    ⊤⁺    _     _ q = q

  trans≈ ⊥⁺    [ _ ] _     (lift ()) _
  trans≈ ⊥⁺    ⊤⁺    _     (lift ()) _
  trans≈ [ _ ] ⊥⁺    _     (lift ()) _
  trans≈ [ _ ] ⊤⁺    _     (lift ()) _
  trans≈ ⊤⁺    ⊥⁺    _     (lift ()) _
  trans≈ ⊤⁺    [ _ ] _     (lift ()) _

  trans≈ [ _ ] [ _ ] ⊥⁺    _ (lift ())
  trans≈ [ _ ] [ _ ] ⊤⁺    _ (lift ())


  compare : Trichotomous _≈⁺_ _<⁺_
  compare [ x ] [ y ] = TO.compare x y

  compare ⊥⁺    [ _ ] = tri< _ lower lower
  compare ⊥⁺    ⊤⁺    = tri< _ lower lower
  compare [ _ ] ⊤⁺    = tri< _ lower lower

  compare ⊥⁺    ⊥⁺    = tri≈ lower _ lower
  compare ⊤⁺    ⊤⁺    = tri≈ lower _ lower

  compare [ _ ] ⊥⁺    = tri> lower lower _
  compare ⊤⁺    ⊥⁺    = tri> lower lower _
  compare ⊤⁺    [ _ ] = tri> lower lower _


  trans : ∀ x y z → x <⁺ y → y <⁺ z → x <⁺ z
  trans [ _ ] [ _ ] [ _ ] p q = TO.trans p q

  trans ⊥⁺    _     [ _ ] _ _ = _
  trans ⊥⁺    _     ⊤⁺    _ _ = _
  trans [ _ ] _     ⊤⁺    _ _ = _

  trans _     ⊥⁺    ⊥⁺    _ (lift ())
  trans _     [ _ ] ⊥⁺    _ (lift ())
  trans _     ⊤⁺    ⊥⁺    _ (lift ())
  trans [ _ ] ⊤⁺    [ _ ] _ (lift ())

  trans [ _ ] ⊥⁺    [ _ ] (lift ()) _
  trans ⊤⁺    ⊥⁺    _     (lift ()) _
  trans ⊤⁺    [ _ ] _     (lift ()) _
  trans ⊤⁺    ⊤⁺    _     (lift ()) _


  respʳ : ∀ x y z → y ≈⁺ z → x <⁺ y → x <⁺ z
  respʳ [ _ ] [ _ ] [ _ ] p q = proj₁ TO.<-resp-≈ p q

  respʳ ⊥⁺    _     [ _ ] _ _ = _
  respʳ ⊥⁺    _     ⊤⁺    _ _ = _
  respʳ [ _ ] _     ⊤⁺    _ _ = _

  respʳ ⊥⁺    ⊥⁺    ⊥⁺    _ (lift ())
  respʳ [ _ ] ⊥⁺    ⊥⁺    _ (lift ())
  respʳ ⊤⁺    _     _     _ (lift ())

  respʳ ⊥⁺    [ _ ] ⊥⁺    (lift ()) _
  respʳ ⊥⁺    ⊤⁺    ⊥⁺    (lift ()) _
  respʳ [ _ ] [ _ ] ⊥⁺    (lift ()) _
  respʳ [ _ ] ⊤⁺    ⊥⁺    (lift ()) _
  respʳ [ _ ] ⊥⁺    [ _ ] (lift ()) _
  respʳ [ _ ] ⊤⁺    [ _ ] (lift ()) _


  respˡ : ∀ x y z → y ≈⁺ z → y <⁺ x → z <⁺ x
  respˡ [ _ ] [ _ ] [ _ ] p q = proj₂ TO.<-resp-≈ p q

  respˡ _     ⊥⁺    ⊥⁺    _ q = q

  respˡ ⊤⁺    [ _ ] [ _ ] _ _ = _

  respˡ ⊥⁺    [ _ ] [ _ ] _ (lift ())
  respˡ _     ⊤⁺    _     _ (lift ())

  respˡ _     ⊥⁺    [ _ ] (lift ()) _
  respˡ _     ⊥⁺    ⊤⁺    (lift ()) _
  respˡ _     [ _ ] ⊥⁺    (lift ()) _
  respˡ _     [ _ ] ⊤⁺    (lift ()) _
