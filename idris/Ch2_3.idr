module Ch2'3

data Desc : Type -> Type where
  Ret  : ix -> Desc ix
  Arg  : (a : Type) -> (a -> Desc ix) -> Desc ix
  Rec  : ix -> Desc ix -> Desc ix
  HRec : ix -> (a : Type) -> Desc ix -> Desc ix

Synthesise : Desc ix -> (ix -> Type) -> ix -> Type
Synthesise (Ret j)      x i = (j = i)
Synthesise (Rec j d)    x i = (rec : x j        ** Synthesise d       x i)
Synthesise (Arg a d)    x i = (arg : a          ** Synthesise (d arg) x i)
Synthesise (HRec j a d) x i = (rec : (a -> x j) ** Synthesise d       x i)

CLabel : Type
CLabel = String

CEnum : Type
CEnum = List CLabel

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

switchDesc :  {e : CEnum} -> {ix : Type}
           -> SPi e (\_ => \_ => Desc ix)
			     -> (l' : CLabel) -> (t' : Tag l' e) -> Desc ix
switchDesc {e} {ix} = switch e (\_ => \_ => Desc ix)

DescDesc : Type -> Desc ()
DescDesc ix =
  Arg CLabel $ \l =>
    Arg (Tag l ["Ret", "Arg", "Rec", "HRec"]) $
      switchDesc
        ( Arg ix $ \_ => Ret ()
        , ( Arg Type $ \a => HRec () a $ Ret ()
          , ( Arg ix $ \_ => Ret ()
            , ( Arg ix $ \_ => Arg Type $ \_ => Rec () $ Ret ()
              , ()
              )
            )
          )
        ) l
