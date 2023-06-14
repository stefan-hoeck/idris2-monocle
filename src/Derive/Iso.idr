module Derive.Iso

import public Derive.Lens.Options
import public Language.Reflection.Util

%default total

isoErr : Either String a
isoErr = Left "Isomorphisms can only be derived for newtypes"

parameters (o : LensOptions)
  iname : ParamTypeInfo -> Name
  iname p = UN $ Basic (o.dataTypeName $ nameStr p.info.name)

  iclaim : Visibility -> ParamTypeInfo -> Name -> TTImp -> Decl
  iclaim vis p con rtpe =
    let arg := p.applied
        tpe := piAll `(Iso' ~(arg) ~(rtpe)) p.implicits
    in simpleClaim vis (iname p) tpe

  idef : ParamTypeInfo -> Name -> Decl
  idef p con =
    let nme := iname p
        get := `(\case ~(var con) x => x)
     in def nme [patClause (var nme) `(I ~(get) ~(var con))]

  itl : Visibility -> ParamTypeInfo -> Con n vs -> Res (List TopLevel)
  itl vis p (MkCon con _ args _) = case boundArgs regular args [] of
    [<arg] => Right [TL (iclaim vis p con arg.arg.type) (idef p con)]
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
