module Derive.Lens

import public Language.Reflection.Util

%default total

lname : Name -> Name
lname n = UN $ Basic (nameStr n ++ "_")

lclaim : Visibility -> ParamTypeInfo -> BoundArg 0 RegularNamed -> Decl
lclaim vis p (BA x _ _) =
  let arg := p.applied
   in simpleClaim vis (lname $ argName x) `(Lens' ~(arg) ~(x.type))

ldef : BoundArg 0 RegularNamed -> Decl
ldef (BA x _ _) =
  let fld := argName x
      nme := lname fld
      u   := update [ISetField [nameStr fld] `(x)] `(y)
   in def nme [patClause (var nme) `(lens ~(var fld) $ \x,y => ~(u))]


||| Generate monomorphic lenses for a record type.
export
LensesVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
LensesVis vis nms p = case p.info.cons of
  [c] => Right (lenses c.args)
  _   => failRecord "Lenses"
  where
    lenses : Vect n Arg -> List TopLevel
    lenses args =
      map (\x => TL (lclaim vis p x) (ldef x)) (boundArgs regularNamed args []) <>> []

||| Alias for `LensesVis Public`
export %inline
Lenses : List Name -> ParamTypeInfo -> Res (List TopLevel)
Lenses = LensesVis Public
