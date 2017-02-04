module Ch2'1'2

import Prelude
%hide List
%hide Nat
%hide Unit

-- 2.1.2

data Desc : Type where
  Ret : Desc
  Arg : (a : Type) -> (a -> Desc) -> Desc
  Rec : Desc -> Desc

data Unit : Type where
  MkUnit : Unit

UnitDesc : Desc
UnitDesc = Ret

data Pair : Type where
  MkPair : Int -> Bool -> Pair

PairDesc : Desc
PairDesc = Arg Int $ \fst => Arg Bool $ \snd => Ret

data Either : Type where
  Right : Int    -> Either
  Left  : String -> Either

EitherDesc : Desc
EitherDesc = Arg Bool $ \isRight =>
               if isRight
               then Arg Int    $ \x => Ret
               else Arg String $ \x => Ret

data Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

NatDesc : Desc
NatDesc = Arg Bool $ \isZero =>
            if isZero
            then Ret
            else Rec Ret

data List : Type -> Type where
  Nil  : List a
  Cons : a -> List a -> List a

ListDesc : Type -> Desc
ListDesc a = Arg Bool $ \isNil =>
               if isNil
               then Ret
               else Arg a $ \x => Rec Ret
