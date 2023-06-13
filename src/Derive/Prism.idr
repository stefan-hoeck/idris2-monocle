module Derive.Prism

import public Derive.Lens.Options
import public Language.Reflection.Util

%default total

parameters (o : LensOptions)
  pname : Name -> Name
  pname n = UN $ Basic (o.constructorName $ nameStr n)

  pclaim : Visibility -> ParamTypeInfo -> Name -> TTImp -> Decl
  pclaim vis p con rtpe =
    let arg := p.applied
        tpe := piAll `(Prism' ~(arg) ~(rtpe)) p.implicits
    in simpleClaim vis (pname con) tpe

  pdef0 : Name -> Decl
  pdef0 con =
    let nme := pname con
        get := `(\case ~(var con) => Just (); _ => Nothing)
     in def nme [patClause (var nme) `(lens ~(get) (const ~(var con)))]

  pdef1 : Name -> Decl
  pdef1 con =
    let nme := pname con
        get := `(\case ~(var con) x => Just x; _ => Nothing)
     in def nme [patClause (var nme) `(lens ~(get) ~(var con))]

  ptl : Visibility -> ParamTypeInfo -> Con n vs -> Maybe TopLevel
  ptl vis p (MkCon con _ args _) = case boundArgs regular args [] of
    [<]    => Just (TL (pclaim vis p con `(Unit))  (pdef0 con))
    [<arg] => Just (TL (pclaim vis p con arg.arg.type) (pdef1 con))
    _      => Nothing

  ||| Generate monomorphic prisms for a sum type.
  export
  PrismsVisO : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
  PrismsVisO vis nms p = Right $ mapMaybe (ptl vis p) p.info.cons

  ||| Alias for `PrismsVisO Public`
  export %inline
  PrismsO : List Name -> ParamTypeInfo -> Res (List TopLevel)
  PrismsO = PrismsVisO Public

||| Alias for `PrismVisO defaultOptions`
export %inline
PrismsVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
PrismsVis = PrismsVisO defaultOptions

||| Alias for `PrismsVis Public`
export %inline
Prisms : List Name -> ParamTypeInfo -> Res (List TopLevel)
Prisms = PrismsVis Public
