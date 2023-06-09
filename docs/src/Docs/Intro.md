# Monocle: An Introduction

This is a short introduction into the monocle library and optics in
general. It is also a literate Idris file and therefore a test for
me whether the library behaves as expected. I therefore start with
the necessary imports.

```idris
module Docs.Intro

import Control.Lens

import Derive.Iso
import Derive.Lens
import Derive.Prelude
import Derive.Prism

%default total
%language ElabReflection
```

## Lenses: Getters and Setters

The monocle library is an optics library. So what are optics?
Optics allow us to focus on one or several pieces of information
in a (possibly deeply nested) data structure. In order to demonstrate
this concept we will first look at *lenses*, arguably the most
important kinds of optics.

The most common type of lenses allow us to focus the individual
fields of a record type:

```idris
record Address where
  constructor A
  street : String
  number : Nat
  city   : String
  state  : String

%runElab derive "Address" [Show,Eq]

streetL : Lens' Address String
streetL = lens street $ \x => {street := x}

numberL : Lens' Address Nat
numberL = lens number $ \x => {number := x}

cityL : Lens' Address String
cityL = lens city $ \x => {city := x}

stateL : Lens' Address String
stateL = lens state $ \x => {state := x}
```

A lens consists of two functions: A function to access the value we
are focussing on (this is also called a *getter*)
and a second function to update or replace the value we
are focussing on (this is also called a *setter*).

Let's have a look at our freshly defined lenses in action:

```idris
address : Address
address = A "Krümelweg" 12 "Bronschofen" "CH"

kruemelweg : String
kruemelweg = get streetL address

moveToGermany : Address
moveToGermany = set stateL "DE" address

increaseNumber : Address
increaseNumber = mod numberL (+2) address
```

As you can see, we can access and update the values in a record
via the corresponding lenses.

There are two issues with what we have seen so far: First, defining
lenses seems to be pretty cumbersome and boring, and second, the
don't seem to add anything new: All of this can be achieved with
record syntax in Idris.

The first issue can be solved with elaborator reflection: The monocle
library provides elaborator scripts to derive the lenses of a record
for us.

About the second issue: The power of lenses and other optics comes
from the ability to compose them to create new optics that focus
on data deep with a nested data structure. Let's introduce a
second record type with a field of type `Address`:

```idris
record Employee where
  constructor E
  name       : String
  age        : Nat
  salary     : Double
  address    : Address
  supervisor : Maybe Employee

%runElab derive "Employee" [Lenses,Show,Eq]
```

The last line includes an instruction to derive the lenses of `Empoyee`
automatically. They will have the same name as the record fields with
an upper-case `'L'` appended (this behavior is customizable).

Let's define to employees, one with a minor error in one of its values:

```idris
helen : Employee
helen = E "Helen" 41 6500 (A "Gutstrasse" 127 "Zürich" "CH") Nothing

john : Employee
john = E "John" 25 5800 (A "Bahnhofstrasse" 12 "Zürich" "ch") (Just helen)
```

As you can see, `john` has the state where he's living given in lower case
letters. Let's fix this:

```idris
johnFixed :  Employee
johnFixed = mod (addressL >>> stateL) toUpper john
```

As you can see, lenses can be composed via the `(>>>)` operator.
However, this is still an example that could easily be solved with
record syntax. We will leave it at that for the time being, but
we will later see, that there are lenses and other optics that
are outside the scope and capabilities of record syntax.

## Iso: Isomorphisms

The second optic we are going to look at is `Iso`, a abbreviation
for *isomorphism*. Isomorphisms connect types that can be converted
in both directions without loss of information. One example is
the isomorphism between `String` and `List Char` (`Control.Iso.unpack`).
Another is the isomorphism between lists and snoclists (`Control.Iso.fish`).

Let's see them in action:

```idris
lastUp : SnocList Char -> SnocList Char
lastUp (i :< l) = i :< toUpper l
lastUp [<]      = [<]

lastToUpper : String -> String
lastToUpper = mod (unpack >>> fish) lastUp
```

Again, this is nothing spectacular, as we could to the same
thing just with function composition. However, lenses and isomorphisms
can be combined (every `Iso` can be converted to a lens with the
`L` utility function). This allows us to use `lastUp` to modify
the nested records we defined in the first section:

```idris
zuericH : Employee
zuericH = mod (addressL >>> cityL >>> L unpack >>> L fish) lastUp john
```

Isomorphisms arise naturally from lossless conversions, for
instance, when we define newtype wrappers:

```idris
record Age where
  constructor MkAge
  value : Nat

%runElab derive "Age" [Show,Eq,FromInteger]

age : Iso' Age Nat
age = I value MkAge
```

Again, we can derive these simple isomorphisms automatically:

```idris
record UserName where
  constructor MkUserName
  value : String

%runElab derive "UserName" [Iso,Show,Eq,FromString]
```

And here's how to make use of them in combination with record updates:

```idris
namespace User
  public export
  record User where
    constructor MkUser
    name : Intro.UserName
    age  : Age

  %runElab derive "User" [Lenses, Show, Eq]

stefan : User
stefan = MkUser "Stefan" 44

olderStefan : User
olderStefan = mod (ageL >>> L age) (+3) stefan
```

## Folds and Setters: Core Optics

Most of the time when working with optics we are interested in either
accessing one or several values in a nested data structure, or updating
such a value. `Fold`s are used for the first use case: They allow us
list and combine (fold) an arbitrary number of values through an optic:

Here's an example: Get the third letter of the name of an employee's supervisor
(if any):

```idris
thirdLetter : Employee -> Maybe Char
thirdLetter =
  first (F supervisorL >>> F just >>> F nameL >>> F unpack >>> F (index 2))
```

`Fold`s are the most basic way of accessing data, and fortunately, all
optics with the exception of `Setter`s can be converted to `Fold`s
via the overloaded `F` utilities. In the example above we see a
combination of lenses `supervisorL` and `nameL`, isomorphism `unpack`.
There are two additional optics, which I'll introduce below: `just` is
a `Prism` and `index 2` is an `Optional`.

While a `Fold` allows us to try and extract a number of values,
a `Setter` allows us to modify such values via a pure function.
The cascade of optics from above can be used to overwrite the
given letter with another one:

```idris
thirdBang : Employee -> Employee
thirdBang =
  set (S supervisorL >>> S just >>> S nameL >>> S unpack >>> S (index 2)) '!'
```

All optics with the exception of `Fold`s and `Getter`s can be converted
to `Setter`s via the overloaded `S` utilities.

## Prisms: Views on Sum Types

While lenses allow us to focus on one or several fields in a
product type, a `Prism` allows us to focus on a single data
constructor in a sum type. We already saw a `Prism` in action
in the examples above: `just`, which focusses on the `Just`
data constructor of `Maybe`.

A `Prism` consists of two functions (which can be passed to the
`prism` utility constructor): A projection function which tries
to extract a wrapped value and an injection function which
wraps a value in the correct data constructor.


<!-- vi: filetype=idris2:syntax=markdown
-->
