module Ch2'1'3

data Desc : Type -> Type where
  Ret : ix -> Desc ix
  Arg : (a : Type) -> (a -> Desc ix) -> Desc ix
  Rec : ix -> Desc ix -> Desc ix

{- Type constructor -}
data Vec          -- Type name
    :  (a : Type) -- Parameter type
    -> Nat        -- Index type
    -> Type where
  {- Data constructors -}
  Nil  : Vec a z
  Cons -- Tag
    {- Data -}
    : {n : Nat} -- Implicit argument
    -> a        -- Explicit argument
    -> Vec a n  -- Recursive argument
    {- Result type -}
    -> Vec
         a     -- Parameter
         (S n) -- Index

VecDesc :  (a : Type) -- Parameter type
        -> Desc
             Nat      -- Index type
VecDesc a =
  {- Data constructor choice -}
  Arg Bool $ \isNil =>
    if isNil
    then Ret Z
    else {- Data description -}
         Arg Nat   -- Argument
           $ \n =>
             Arg a -- Argument
             $ \x =>
             Rec n -- Recursive argument
                 {- Result type description -}
                 (Ret
                   (S n)) -- Index
