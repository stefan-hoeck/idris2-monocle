module Derive.Iso

import public Derive.Lens.Options
import public Language.Reflection.Util

%default total

isoErr : Either String a
isoErr = Left "Isomorphisms can only be derived for newtypes"

parameters (o : LensOptions)
  iname : Name -> Name
  iname n = UN $ Basic (o.dataTypeName $ nameStr n)

  iclaim : Visibility -> ParamTypeInfo -> Name -> TTImp -> Decl
  iclaim vis p con tpe =
    let arg := p.applied
    in simpleClaim vis (iname con) `(Iso' ~(arg) ~(tpe))

  idef : Name -> Decl
  idef con =
    let nme := iname con
        get := `(\case ~(var con) x => x)
     in def nme [patClause (var nme) `(I ~(get) ~(var con))]

  itl : Visibility -> ParamTypeInfo -> Con n vs -> Res (List TopLevel)
  itl vis p (MkCon con _ args _) = case boundArgs regular args [] of
    [<arg] => Right [TL (iclaim vis p con arg.arg.type) (idef con)]
    _      => isoErr

  ||| Generate an isomorphism for a newtype
  export
  IsoVisO : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
  IsoVisO vis nms p = case p.info.cons of
    [c] => itl vis p c
    _   => isoErr

  ||| Alias for `IsoVisO Public`
  export %inline
  IsoO : List Name -> ParamTypeInfo -> Res (List TopLevel)
  IsoO = IsoVisO Public

||| Alias for `IsoVisO defaultOptions`
export %inline
IsoVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
IsoVis = IsoVisO defaultOptions

||| Alias for `IsoVis Public`
export %inline
Iso : List Name -> ParamTypeInfo -> Res (List TopLevel)
Iso = IsoVis Public
