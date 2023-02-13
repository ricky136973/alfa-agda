open import prelude
open import core

module statics where
  data Ctx : Set where
    ·      : Ctx
    _,_::_ : Ctx → String → Typ → Ctx

  data _::_∈_ : String → Typ → Ctx → Set where
    here  : ∀ {x τ Γ}
      → x :: τ ∈ (Γ , x :: τ)
    there : ∀ {x₁ τ₁ x₂ τ₂ Γ}
      → (x₁ ≡ x₂ → ⊥)
      → x₁ :: τ₁ ∈ Γ
      --------------------------
      → x₁ :: τ₁ ∈ (Γ , x₂ :: τ₂)

  data _⊢_::_ : Ctx → Exp → Typ → Set where
    T-NumLit : ∀ {Γ n}
      → Γ ⊢ NumLit n :: Num
    T-Neg : ∀ {Γ e}
      → Γ ⊢ e :: Num
      --------------------------
      → Γ ⊢ EUnOp Neg e :: Num
    T-Plus : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Plus e₁ e₂ :: Num
    T-Minus : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Minus e₁ e₂ :: Num
    T-Times : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Times e₁ e₂ :: Num
    T-Lt : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Lt e₁ e₂ :: Bool
    T-Gt : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Gt e₁ e₂ :: Bool
    T-Eq : ∀ {Γ e₁ e₂}
      → Γ ⊢ e₁ :: Num
      → Γ ⊢ e₂ :: Num
      --------------------------
      → Γ ⊢ EBinOp Eq e₁ e₂ :: Bool
    T-True : ∀ {Γ}
      → Γ ⊢ True :: Bool
    T-False : ∀ {Γ}
      → Γ ⊢ False :: Bool
    T-If : ∀ {Γ τ e₁ e₂ e₃}
      → Γ ⊢ e₁ :: Bool
      → Γ ⊢ e₂ :: τ
      → Γ ⊢ e₃ :: τ
      --------------------------
      → Γ ⊢ If e₁ e₂ e₃ :: τ
    T-Var : ∀ {Γ x τ}
      → x :: τ ∈ Γ
      --------------------------
      → Γ ⊢ Var x :: τ
    T-LetAnn : ∀ {Γ x τ₁ τ₂ e₁ e₂}
      → Γ ⊢ e₁ :: τ₁
      → (Γ , x :: τ₁) ⊢ e₂ :: τ₂
      --------------------------
      → Γ ⊢ LetAnn τ₁ e₁ x e₂ :: τ₂
    T-Fun : ∀ {Γ x τᵢ τₒ e}
      → (Γ , x :: τᵢ) ⊢ e :: τₒ
      --------------------------
      → Γ ⊢ Fun τᵢ x e :: Arrow τᵢ τₒ
    T-Ap : ∀ {Γ τᵢ τₒ e₁ e₂}
      → Γ ⊢ e₁ :: Arrow τᵢ τₒ
      → Γ ⊢ e₂ :: τᵢ
      --------------------------
      → Γ ⊢ EBinOp Ap e₁ e₂ :: τₒ
