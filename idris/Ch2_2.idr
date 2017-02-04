module Ch2_2

data Desc : Type -> Type where
  Ret : ix -> Desc ix
  Arg : (a : Type) -> (a -> Desc ix) -> Desc ix
  Rec : ix -> Desc ix -> Desc ix

Synthesise : Desc ix -> (ix -> Type) -> ix -> Type
Synthesise (Ret j)   x i = (j = i)
Synthesise (Rec j d) x i = (rec : x j ** Synthesise d x i)
Synthesise (Arg a d) x i = (arg : a   ** Synthesise (d arg) x i)

data Data : {ix : Type} -> Desc ix -> ix -> Type where
  Con :  {d : Desc ix} -> {i : ix}
      -> Synthesise d (Data d) i -> Data d i

CLabel : Type
CLabel = String

CEnum : Type
CEnum = List CLabel

VecCtors : CEnum
VecCtors = ["Nil", "Cons"]

data Tag : CLabel -> CEnum -> Type where
  TZ : Tag l (l :: e)
  TS : Tag l e -> Tag l (l' :: e)

SPi :  (e : CEnum)
    -> ((l : CLabel) -> Tag l e -> Type)
    -> Type
SPi []       _    = ()
SPi (l :: e) prop = (prop l TZ, SPi e $ \l' => \t => prop l' $ TS t)

switch :  (e : CEnum)
       -> (prop : (l : CLabel) -> (t : Tag l e) -> Type)
       -> SPi e prop
       -> (l' : CLabel) -> (t' : Tag l' e) -> prop l' t'
-- NB: Don't use the name "l'" for the first element of the CEnum, or you'll
-- trigger https://github.com/idris-lang/Idris-dev/issues/3651
switch (l :: e) prop (propz, props) l  TZ      = propz
switch (l :: e) prop (propz, props) l' (TS t') =
  switch e (\l => \t => prop l (TS t)) props l' t'

VecDesc : Type -> Desc Nat
VecDesc a =
  Arg CLabel $ \l =>
    Arg (Tag l VecCtors) $
      switch VecCtors (\_ => \_ => Desc Nat)
        ( Ret Z
        , ( Arg Nat $ \n => Arg a $ \_ => Rec n $ Ret $ S n
          , ()
          )
        ) l

Vec : (a : Type) -> Nat -> Type
Vec a n = Data (VecDesc a) n

exampleVecUgly : Vec Char 3
exampleVecUgly = Con ("Cons" ** (TS TZ ** (2 ** ('1' **
                  (Con ("Cons" ** (TS TZ ** (1 ** ('2' **
                    (Con ("Cons" ** (TS TZ ** (0 ** '3' **
                      (Con ("Nil" ** (TZ ** Refl)) ** Refl)
                      )))) ** Refl)
                    )))) ** Refl)
                 )))

Nil : {a : Type} -> Vec a Z
Nil = Con ("Nil" ** (TZ ** Refl))

Cons :  {a : Type} -> {n : Nat}
     -> a -> Vec a n -> Vec a (S n)
Cons {n} x xs = Con ("Cons" ** (TS TZ ** (n ** (x ** (xs ** Refl)))))

-- I would use Vec Nat 3 here, but that tickles
-- https://github.com/idris-lang/Idris-dev/issues/3652
exampleVecIdeal : Vec Char 3
exampleVecIdeal = Cons '1'
                $ Cons '2'
                $ Cons '3' Nil
