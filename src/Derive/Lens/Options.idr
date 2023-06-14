module Derive.Lens.Options

import Data.String

%default total

public export
record LensOptions where
  constructor LO
  fieldName :       String -> String
  constructorName : String -> String
  dataTypeName    : String -> String

export
toLowerHead : String -> String
toLowerHead s = case strM s of
  StrNil       => s
  StrCons x xs => singleton (toLower x) ++ xs

export
defaultOptions : LensOptions
defaultOptions = LO (++ "L") toLowerHead (\x => toLowerHead x ++ "I")
