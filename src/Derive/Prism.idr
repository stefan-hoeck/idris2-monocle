module Derive.Prism

import public Language.Reflection.Util

%default total

pname : Name -> Name
pname n = UN $ Basic (toLower $ nameStr n)

pclaim : Visibility -> ParamTypeInfo -> Name -> TTImp -> Decl
pclaim vis p con tpe =
  let arg := p.applied
  in simpleClaim vis (pname con) `(Prism' ~(arg) ~(tpe))

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
PrismsVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
PrismsVis vis nms p = Right $ mapMaybe (ptl vis p) p.info.cons

||| Alias for `PrismsVis Public`
export %inline
Prisms : List Name -> ParamTypeInfo -> Res (List TopLevel)
Prisms = PrismsVis Public
