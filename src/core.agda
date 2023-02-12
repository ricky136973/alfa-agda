open import prelude

module core where
  data Typ : Set where
    Num   : Typ
    Bool  : Typ
    Arrow : Typ → Typ → Typ

  data UnOp : Set where
    Neg : UnOp

  data BinOp : Set where
    Lt    : BinOp
    Gt    : BinOp
    Eq    : BinOp
    Plus  : BinOp
    Minus : BinOp
    Times : BinOp
    Ap    : BinOp
  
  data Exp : Set where
    NumLit : Int → Exp
    True   : Exp
    False  : Exp
    EUnOp  : UnOp → Exp → Exp
    EBinOp : BinOp → Exp → Exp → Exp
    If     : Exp → Exp → Exp → Exp
    Var    : String → Exp
    LetAnn : Typ → Exp → String → Exp → Exp
    Fun    : Typ → String → Exp → Exp
