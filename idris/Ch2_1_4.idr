module Ch2'1'4Through5

-- 2.1.4

CLabel : Type
CLabel = String

CEnum : Type
CEnum = List CLabel

VecCtors : CEnum
VecCtors = ["Nil", "Cons"]

data Tag : CLabel -> CEnum -> Type where
  TZ : Tag l (l :: e)
  TS : Tag l e -> Tag l (l' :: e)

NilTag : Tag "Nil" VecCtors
NilTag = TZ

ConsTag : Tag "Cons" VecCtors
ConsTag = TS TZ

-- 2.1.5

SPi :  (e : CEnum)
    -> ((l : CLabel) -> Tag l e -> Type)
    -> Type
SPi []       _    = ()
SPi (l :: e) prop = (prop l TZ, SPi e $ \l' => \t => prop l' $ TS t)

switch :  (e : CEnum)
       -> (prop : (l : CLabel) -> (t : Tag l e) -> Type)
       -> SPi e prop
       -> (l' : CLabel) -> (t' : Tag l' e) -> prop l' t'
switch (l' :: e) prop ((propz, props)) l' TZ      = propz
switch (l  :: e) prop ((propz, props)) l' (TS t') =
  switch e (\l => \t => prop l (TS t)) props l' t'
