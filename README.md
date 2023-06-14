# idris2-monocle: A simple Optics library for Idris

Optics allow us to inspect and update deeply nested data
structures in a concise and convenient manner. However,
depending on how they are encoded, they can be hard to understand
for the uninitiated and can lead to cryptic error messages from
the compiler in the case of type errors. The design space for
implementing an optics library is therefore pretty large:
Several such libraries exist for instance for the Haskell
programming language.

## Usage Example

A `Lens` is probably the core data type of an optics library.
It allows us to inspect and modify a certain piece of information
in a - possibly deeply - nested data structure.

```idris
module Docs.README

import Monocle
import Derive.Lens
import Derive.Prelude

%default total
%language ElabReflection

record Address where
  constructor A
  street : String
  number : Nat
  city   : String
  state  : String

%runElab derive "Address" [Lenses,Show,Eq]

record Employee where
  constructor E
  name       : String
  age        : Nat
  salary     : Double
  address    : Address
  supervisor : Maybe Employee

%runElab derive "Employee" [Lenses,Show,Eq]
```
In the following piece of code we are going to change
the state of all employees living in Zurich to `"CH"`:

```idris
adjState : List Employee -> List Employee
adjState = set (list_ .> addressL .> eqBy "Zürich" city .> stateL) "CH"
```

The example above makes use of several optics: `list_` is a `Traversal` working
on the individual values in a list, `addressL` is a `Lens`
auto-generated for data type `Employee`, `eqBy` is an `Optional`, and
`stateL` is another `Lens`. Sequencing these via `(.>)` yield a `Traversal`,
which is the converted to a `Setter` when being passed to `set`.

## Design Decisions

There is already at least one other optics library
([idris2-lens](https://github.com/kiana-S/idris2-lens)) and there might follow additional
libraries because the design space for implementing optics is pretty large.

To be continued...

<!-- vi: filetype=idris2:syntax=markdown
-->
