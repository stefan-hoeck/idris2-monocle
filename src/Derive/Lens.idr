module Derive.Lens

import public Derive.Lens.Options
import public Language.Reflection.Util

%default total

parameters (o : LensOptions)
  lname : Name -> Name
  lname n = UN $ Basic (o.fieldName $ nameStr n)

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
  LensesVisO : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
  LensesVisO vis nms p = case p.info.cons of
    [c] => Right (lenses c.args)
    _   => Left "Lenses can only be derived for record types"
    where
      lenses : Vect n Arg -> List TopLevel
      lenses args =
        map (\x => TL (lclaim vis p x) (ldef x)) (boundArgs regularNamed args []) <>> []

  ||| Alias for `LensesVisO Public`
  export %inline
  LensesO : List Name -> ParamTypeInfo -> Res (List TopLevel)
  LensesO = LensesVisO Public

||| Alias for `LensesVisO defaultOptions`
export %inline
LensesVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
LensesVis = LensesVisO defaultOptions

||| Alias for `LensesVis Public`
export %inline
Lenses : List Name -> ParamTypeInfo -> Res (List TopLevel)
Lenses = LensesVis Public
