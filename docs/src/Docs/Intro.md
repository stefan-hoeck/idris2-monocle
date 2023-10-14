# Monocle: An Introduction

This is a short introduction into the monocle library and optics in
general. It is also a literate Idris file and therefore a test for
me whether the library behaves as expected. I therefore start with
the necessary imports.

```idris
module Docs.Intro

import Monocle

import Derive.Iso
import Derive.Lens
import Derive.Prelude
import Derive.Prism

import JSON.Simple.Derive

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

%runElab derive "Address" [Show,Eq,FromJSON,ToJSON]

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
kruemelweg = to streetL address

moveToGermany : Address
moveToGermany = set stateL "DE" address

increaseNumber : Address
increaseNumber = over numberL (+2) address
```

As you can see, we can access (function `to`) and
update (functions `set` and `over`) the values in a record
via the corresponding lenses.

There are two issues with what we have seen so far: First, defining
lenses seems to be pretty cumbersome and boring, and second, they
don't seem to add anything new: All of this can be achieved with
record syntax in Idris.

The first issue can be solved with elaborator reflection: The monocle
library provides elaborator scripts to derive the lenses of a record
for us.

About the second issue: The power of lenses and other optics comes
from the ability to sequence them to create new optics that focus
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

%runElab derive "Employee" [Lenses,Show,Eq,FromJSON,ToJSON]
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
johnFixed = over (addressL .> stateL) toUpper john
```

As you can see, lenses can be composed via the `(.>)` operator.
However, this is still an example that could easily be solved with
record syntax. We will leave it at that for the time being, but
we will later see, that there are lenses and other optics that
are outside the scope and capabilities of record syntax.

## Iso: Isomorphisms

The second optic we are going to look at is `Iso`, an abbreviation
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
lastToUpper = over (unpack .> fish) lastUp
```

Again, this is nothing spectacular, as we could do the same
thing just with function composition. However, lenses and isomorphisms
can be combined (every `Iso` can be converted to a lens via interface
`ToLens`). This allows us to use `lastUp` to modify
the nested records we defined in the first section:

```idris
zuericH : Employee
zuericH = over (addressL .> cityL .> unpack .> fish) lastUp john
```

The example above shows an important concept: Operator `(.>)` is overloaded,
and allows us to sequence different types of optics. The type of the resulting
optic is computed automatically.

Isomorphisms arise naturally from lossless conversions, for
instance, when we define newtype wrappers:

```idris
record UserName where
  constructor MkUserName
  value : String

%runElab derive "UserName" [Show,Eq,FromString,FromJSON,ToJSON]

userNameI : Iso' Intro.UserName String
userNameI = I value MkUserName
```

Again, we can derive these simple isomorphisms automatically:

```idris
record Age where
  constructor MkAge
  value : Nat

%runElab derive "Age" [Iso,Show,Eq,FromInteger,FromJSON,ToJSON]
```

And here's how to make use of them in combination with record updates:

```idris
namespace User
  public export
  record User where
    constructor MkUser
    name : Intro.UserName
    age  : Age

  %runElab derive "User" [Lenses, Show, Eq,FromJSON,ToJSON]

stefan : User
stefan = MkUser "Stefan" 44

olderStefan : User
olderStefan = over (User.ageL .> ageI) (+3) stefan
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
thirdLetter = first (supervisorL .> just .> nameL .> unpack .> ix 2)
```

`Fold`s are the most basic way of accessing data, and fortunately, all
optics with the exception of `Setter`s can be converted to `Fold`s
via the `ToFold` interface. In the example above we see a
combination of lenses `supervisorL` and `nameL`, and isomorphism `unpack`.
There are two additional optics, which I'll introduce below: `just` is
a `Prism` and `index 2` is an `Optional`. The sequencing of these results
in an `Optional`, which will then be converted to a `Fold` in the
call to `first`.

While a `Fold` allows us to try and extract a number of values,
a `Setter` allows us to modify such values via a pure function.
The cascade of optics from above can be used to overwrite the
given letter with another one:

```idris
thirdBang : Employee -> Employee
thirdBang = set (supervisorL .> just .> nameL .> unpack .> ix 2) '!'
```

All optics with the exception of `Fold`s and `Getter`s can be converted
to `Setter`s via interface `ToSetter`.

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

Besides sum types, there are many situations where a `Prism` is
appropriate. For instance, we can define a prism from `String`
to JSON-encoded values:

```idris
json : FromJSON a => ToJSON a => Prism' JSON a
json = prism (either (const Nothing) Just . fromJSON) toJSON

parseJSON : Prism' String JSON
parseJSON = prism (either (const Nothing) Just . parseJSON Virtual) show

codec : FromJSON a => ToJSON a => Prism' String a
codec = parseJSON .> json
```

Let's give this a go:

```idris
incEncodedAge : String -> String
incEncodedAge = over (codec .> Intro.ageL) (+1)

encodedEmployee : String
encodedEmployee = """
  {
    "name"       : "John",
    "age"        : 33,
    "salary"     : 5300,
    "supervisor" : null,
    "address"    : {
      "street" : "Here" ,
      "number" : 123,
      "city"   : "London",
      "state"  : "GB"
    }
  }
  """
```

Go ahead, and give this a try at the REPL: `incEncodedAge encodedEmployee` will
increase the encoded employee's age and return a new string with the JSON data.

In the example above, we go via a proper Idris type, which we can encode to
and decode from JSON. It is also possible to achieve the same result by using
derived prisms for the `JSON` sum type:

```idris
%runElab derive "JSON" [Prisms]
```

The elaborator script above generates prisms of the same name as the data
constructors of `JSON` (but starting with a lower-case letter), such
as `jNull` or `jString`.

```idris
key : String -> Optional' (List (String,a)) a
key s = first ((s ==) . fst) .> snd

inc : Num a => a -> a
inc = (+1)

incEncodedAge2 : String -> String
incEncodedAge2 = over (parseJSON .> jObject .> key "age" .> jInteger) inc
```

Let's have a look at these: `key` allows us to focus on a specific
key-value pair in a list of pairs. Here, we make use of
`Monocle.Optional.first`, for focussing on the first value in a list
that fulfills a given predicate. In order to only look at the second
value of the resulting pair, we use `Monocle.Lens.snd`.

By combining this with several prisms, we can conveniently parse and
update the JSON string.

At first, we found that `Getter`s and `Fold`s can often be replaced with
simple (pure) functions, but in the current example, even this gets tedious.
With optics, however, we can use the same optics for updating and
extracting values. In the example above, we could move the
`Optional` to the top-level and use it for updating and accessing data:

```idris
ageO : Optional' String Nat
ageO = parseJSON .> jObject .> key "age" .> jInteger .> nat
```

We can now extract the age of an encoded employee like so:
`first ageO encodedEmployee`.

## Optional: A View on Things that might not be there

There are only a few views left for us to cover, but this one is also highly
useful. Assume we got a list of employees and would like to increase the
salary of all whose age is above 40. Here's how to do that:

```idris
increased : List Employee
increased = over (list_ .> select ((> 40) . age) .> salaryL) (+100) [helen,john]
```

In the example above, Helen's salary will be increased while John's won't.
Traversal `list_` operates on the values in a list, while `select` defines
an `Optional` that only returns or updates a value if it fulfills the
given predicate.

`Optional`s are slightly less powerful than `Prism`s (every `Prism`
can be converted to an `Optional` by means of the `ToOptional` interface).

Note: The `select` `Optional` we used above is somewhat controversial, as
it allows us to define non-lawful optics. I'll cover this topic in
a later section, but suffice to say that we should not filter on
a piece of information we plan to modify with the same optic. In the
example above, we are fine: We filter on age but we modify the salary.

## Traversal: An Optic for effectful Traversals

The last optic we are going to look at is the `Traversal`. It is highly
useful when working with container types potentially holding many values.
We already saw an example in function `increased`, where we used the
`list_` traversal.

<!-- vi: filetype=idris2:syntax=markdown
-->
