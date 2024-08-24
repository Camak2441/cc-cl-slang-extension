
# $!'ANG

`$!'ANG` is an extension of SLANG to add several fun and interesting features, primarily lazy evaluation, with lists (and sequences by laziness), multi variable lambdas and lets as a secondary additions. `$!'ANG` achieves this by a new data type, the thunk type, which allows for an unevaluated value to be held. It then implicitly evaluates the thunk at relevant locations determined at compile time.

## Thunk Evaluation Rules

A thunk is created by the `'` operator, which will avoid evaluating the expression after it, instead choosing to return it as a thunk. Thunks are often made by evaluating a value, and generating a function which returns that constant. Since this is always done implicitly, the programmer cannot explicitly construct thunks this way. Thunks can be strictly evaluated by the strict operator `$!`. Note that attempting to apply the strict operator to a non-thunk does nothing (the emitted code does not even have the strict operation applied). Thunks will be implicitly evaluated in two primary contexts: being put in a non-thunk container of the same underlying type, or by being used by some operation for determining behaviour.

The first behaviour allows users to ensure that certain functions or objects receive their arguments strictly. This is demonstrated by the following example:

```$!'ANG
let x : int ref = ref 0 in
let f (y: int): int = begin (x := !x + 1); y end in
let g (y: int thunk): int = begin (x := !x + 1); y end in
let a: int thunk = '!x in
begin
(f a) + (g a) + (f a)
end
```

The result of running this code is `4`, because when `a` is passed to `f`, it is passed strictly since `f`'s parameters are strict, and therefore the increments to `x` within `f` do not affect the final result, unlike the increments in `g` which do, since `y` is passed lazily.

The second behaviour allows users to easily use thunks without having to explicitly evaluate them. This is demonstrated by the following example:

```$!'ANG
let x : int ref = ref 777 in
let a : int thunk = !x in
let b : int thunk = '!x in
begin
x := 101;
a + b
end
```

Here `a` and `b` are implicitly evaluated before being added, since the behaviour of addition depends on the values in `a` and `b`.

This in combination with sequences can allow for code to implicitly evaluate values as needed, making it easy to create infinite sequences without a lot of boilerplate.

(Note that `hd`, and `tl` are head and tail respectively)

```$!'ANG
let n (x: int): int seq = 
  x :: '(n (x + 1))
in
let sumfirst (x: int) (l: int seq): int = 
  if 0 < x then 
    (;: l) + sumfirst (x - 1) (:; l)
  else 0
in
let l : int seq = n 1 in begin
sumfirst (?) l
end
```

This code calculates the sum of the first n natural numbers (0 based), where n is the user input. It does this by producing a sequence for the naturals, and consuming it until all of the required numbers have been consumed. Under the hood, a sequence has two constructors, EMPTY, and CONS of `'a * 'a seq thunk`. This means that the `tl l` actually returns an object of type `'a seq thunk`. This however is evaluated when passed back into `sumfirst`, since `sumfirst` expects a strict sequence, so the sequence is immediately evaluated.

```$!'ANG
let n (x: int): int seq = 
  x :: '(n (x + 1))
in
let sumfirst (x: int) (l: int seq thunk): int = 
  if 0 < x then 
    (;: l) + sumfirst (x - 1) (:; l)
  else 0
in
let l : int seq = n 1 in begin
sumfirst (?) l
end
```

The alternative form presented here has a thunk as the argument to the function. This results in sumfirst being passed the thunk, rather than the evaluated value. This thunk is eventually used in the expression `hd l`. Since the behaviour (whether the program returns a value or crashes due to trying to get the head of an empty list) is dependent on the value of `l`, `l` is evaluated here instead.

In both cases, the sequence is elegantly evaluated when needed.

## Implementation

Thunks were implemented by using unit argument functions, which are essentially continuations. These are evaluated with the added jargon instruction STRICT, which is a function call where no arguments are given. Despite the fact it is essentially equivalent to calling a function with unit, this instruction is kept for efficiency and legacy reasons. Initially, thunks were not explicitly typed, and so whether the value needed to be evaluated was decided at runtime, requiring tags to note that thunk functions were in fact thunks, and a special STRICT instruction to check that tag. This has been replaced by a static system, where the evaluation strategy of a value was in its type information. This allows for the static generation of when to strict a value, and when not to strict a value.

Since the language now infers when to evaluate thunk types statically, rules were made for when thunks would be evaluated, especially with regards to lambda functions which do not have the return type tagged, and therefore could either evaluate the result locally, or return a thunk. This involved the use of a new type inference function, which had a target type. This allows a surrounding context's required type to alter whether the returned value is returned lazily or strictly. Generally `$!'ang` will push down the decision as deep into the tree as possible. For example, a lambda used in a context where it is expected to return a strict value will automatically evaluate the return value before returning it. 

For the higher level interpreters, LAZY and STRICTTHUNK instructions were often required, since the structure of a thunk varied from the structure of a regular function. LAZY created a thunk for a given expression, and STRICTTHUNK made a thunk for a value. These have also been kept because STRICTTHUNK allowed for thunks returning constant values to share code. 

Since most of the decisions on when to STRICT are decided by the type checker, the interpreters do not need to have much logic to handle the new behaviours, with most of the future plans regarding improving thunk behaviours being on improving the static code generation.

## Future Updates

The type inference now parses in expected values for certain expressions, which it can then use to make better decision on when to strict something, allowing lambda functions to correctly choose whether to strict something or not. This is not completely implemented yet: several functions (notably the list related functions) have not yet had their inference rules completed. This could be extended to allow for let binders to infer the types of their bodies, instead of having it explicitly declared.

## Known Issues

Currently, only interpreters 0, 2, 3, and 4 have actually been altered to run the updated version of the language. Interpreter 2 currently does not handle lists and references correctly, likely in relation to recursively defined functions. Since 2 is not the lowest level interpreter, fixing it is currently very low priority (in comparison to improving the type inference which would improve all interpreters).
