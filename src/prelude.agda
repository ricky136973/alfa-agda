module prelude where
  open import Agda.Builtin.Int public
  open import Agda.Builtin.String public
  open import Agda.Builtin.Equality public

  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  data ⊥ : Set where
  data ⊤ : Set where
    tt : ⊤

  absurd : ∀ {A : Set} → ⊥ → A
  absurd ()
