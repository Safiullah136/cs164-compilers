# HW 1

## Introduction

In this homework, you'll be implementing interpreters and compilers for two
languages capable of basic arithmetic:

- `bin`: a language supporting integers and binary `+` and `*` operators.

  **Example programs:** `1260`, `(+ 1 2)`, `(* 3 4)`, `(+ (* 3 5) (+ 10 2))`

- `variadic`: a language supporting integers and variadic `+` and `*`
  operators (i.e. operators able to accept **any** number of arguments).

  **Example programs:** `(*)`, `(+ 1)`, `(* 5 6 6 7)`, `(+ 3 2 (* 4 5 6))`

### Background

*S-expressions* are a lightweight syntax to represent tree-like data structures
We will use them as the syntax of the languages we will be implementing in HW 1.
An S-expression can take one of two forms: an "atom", or (recursively) a list of
zero or more space-separated s-expressions all surrounded by a pair of
parentheses. For our purposes, we will take an "atom" to be either a number or a
string of characters (a "symbol").

The example programs above are all examples of s-expressions. We can also
construct valid s-expressions that do not correspond to any valid program in
`bin` or `variadic`, for example:

- `(hello world)`
- `()`
- `(/ 2 3)`

### Provided code

The `lib` directory will contain the code for your compilers and interpreters.
The `s_exp` directory provides basic functionality for working with
S-expressions (described in the next paragraph). The `test`  directory will
contain all the tests for your code. In this homework, you will need to modify
files in the `lib` and the `test` directories, but you need not open the `s_exp`
directory.

The `s_exp` directory contains the `S_exp` module, which contains types and
functions for working with s-expressions. (The implementation relies on some
external tools, so you don't need to worry about how the parsing is implemented
under the hood!)

We represent s-expressions with the `s_exp` type:

```ocaml
type s_exp
  = Num of int
  | Sym of string
  | Lst of t list
```

To parse an expression from a string, we provide the `parse` function:

```ocaml
parse : string -> s_exp
```

Additionally, you can produce a debugging representation of an expression with
the provided `show` function:

```ocaml
show : s_exp -> string
```

### OCaml syntax is...

Let's face it: OCaml syntax is weird! Semicolons in lists instead of commas, `=`
for equality instead of `==`, using parentheses or `begin`/`end` around nested
`match` expressions, and much more. Moreover, OCaml can be quite terse:
even though you end up with small snippets of code at the end, it can take a
while to figure out how to break things down to read and write the code.

Getting stuck on these issues is totally okay! Please feel free to post on
Piazza any confusing syntax or come into office hours.

## Grading

For this homework and every homework going forward, we will not provide you
with all the test cases that the autograder will run on your code. This means
that you will need to write your own tests to be confident of the correctness
of your code! In fact, there are even some exercises that require you to write
tests, and we **will** be grading these exercises. We will do so by running your
tests on buggy implementations of the functions that you are testing and
checking to see if your tests capture the bugs.

**Note:** All numbers that we test will be between -1000 and 1000, so do not
worry about handling integer overflow and underflow. When writing your tests,
do not attempt to exploit overflow or underflow.

### Modifying files

Please do **NOT** modify any files other than `lib/arith.ml` and
`test/test_arith.ml`. You are free to use any helper functions that you wish,
but please make sure that the helper functions for `lib/arith.ml` are present
in `lib/arith.ml` and similarly for `test/test_arith.ml`.

### Submission

Please see
[this question](https://inst.eecs.berkeley.edu/~cs164/fa25/faq.html#submission)
on the course FAQ for a reminder on how to submit this assignment!

## Useful commands

- `dune build` builds everything.
- `dune runtest -f` runs the tests in the `test/` directory.
- `dune runtest --watch` runs the tests in the `test/` directory on every save.
- `dune utop` runs a toplevel. You can access the functions you're developing for
  this homework by running, e.g.,

```shell
# dune utop
utop> open Lib.Arith;;
utop> string_of_s_exp (Num (-45));;
"-45"
```

## Tasks

**Note:** All functions you must implement are defined with `let`, but you may
change any of them to `let rec` as you see fit.

### Task 1: Stringifying expressions (1 subtask)

**Task 1.1:** To get some practice working with the `s_exp` type, implement the
`string_of_s_exp` function in `lib/arith.ml`, which should produce the string
representation of the expression it is given. For example,

- `string_of_s_exp (Lst [])` should be `"()"`
- `string_of_s_exp (Num 42)` should be `"42"`
- `string_of_s_exp (Sym "a")` should be `"a"`
- `string_of_s_exp (Sym "a")` should be `"a"`
- `string_of_s_exp (Lst [Sym "a"; Sym "b"])` should be `"(a b)"`
- `string_of_s_exp (Lst [Sym "+"; Num 3; Lst [Sym "*"; Num 4; Num 5]])` should be `"(+ 3 (* 4 5))"`

For this function only, we have included tests for you in `test/test_s_exp.ml`
in the function `test_string_of_s_exp`.

**Hint:** The `string_of_int` function converts an integer to a string.

**Hint:** The [`String.concat`](https://ocaml.org/api/String.html#VALconcat)
function may be helpful!

### Task 2: Bin (9 subtasks)

As described above, `bin` is a language that supports integers and binary `+`
and `*` operators.

The grammar of `bin` is as follows:

```bnf
<expr> ::= <num>
         | (+ <expr> <expr>)
         | (* <expr> <expr>)
```

**Note:** Additional parentheses are _not_ allowed; e.g., `((1))` is not a valid
`bin` program.

**Task 2.1:** In `test/test_arith.ml`, write tests for the
as-of-yet-unimplemented function `is_bin : s_exp -> bool` that determines
whether or not an s-expression is a valid `bin` expression.

Two provided testing functions you might find useful are `assert_equal` and
`assert_raises`. Here is an example of their usage:

```ocaml
(* Asserts that the two arguments must be equal *)
assert_equal (1 + 2) 3

(* Asserts that the exception specified in the first argument will
be raised by running the second argument (a thunk) *)
assert_raises Division_by_zero (fun () -> 1 / 0)
```

Additionally, `assert_equal` takes an optional `printer` parameter that
specifies how to print the arguments if the test fails. Example usage is as
follows:

```ocaml
(* Without printer argument *)
assert_equal 10 15
(* Results in "Failure: not equal" *)

(* With printer argument *)
assert_equal ~printer:string_of_int 10 15
(* Results in "Failure: expected: 10 but got: 15" *)
```

**Task 2.2:** In `lib/arith.ml`, implement the function `is_bin`.

To get a value out of a `bin` expression, we'll explore two options:

-   Directly _interpret_ the expression, performing the arithmetic operations as
    we go, to produce a value. For example, we would interpret `(+ 1 2)` in
    OCaml as `1 + 2`, which produces `3`.
-   _Compile_ the expression into a lower-level sequence of instructions, which
    can then be evaluated to produce a value.

**Task 2.3:** In `test/test_arith.ml`, write tests for the
as-of-yet-unimplemented function `interp_bin : s_exp -> int` that takes the
first approach to evaluate expressions. If an expression cannot be evaluated,
`interp_bin` should raise the `Stuck` exception.

**Task 2.4:** In `lib/arith.ml`, implement the function `interp_bin`.

The second approach, compiling expressions to instructions requires a definition
of "instruction".  We'll use this one:

```ocaml
type instr
  = Push of int
  | Add
  | Mul
```

A `Push` instruction takes an integer and _pushes_ it onto a _stack_, a list of
integers that serves as the working memory of whatever is evaluating the
instructions. Instructions that operate on arguments (in this case `Add` and
`Mul`, which each require two arguments), _pop_ them from the stack as needed.
Stacks are last-in-first-out, meaning that a pop will remove the value
most-recently added to the stack. For convenience, a `stack` type is defined as
an alias for `int list`.

**Note:** For the following tasks, the order in which you push operands to the
stack do not matter as addition and multiplication are both _commutative_, i.e.,
`a + b` is the same as `b + a` (and likewise for multiplication). You may
assume any stack ordering behavior that you prefer in your implementation and
tests (i.e., your tests don't need to handle other stack orderings).

**Task 2.5:** In `test/test_arith.ml`, write tests for the following
as-of-yet-unimplemented functions:

1. `interp_instr : stack -> instr -> stack`, which interprets an instruction in
   the context of a stack  to produce an updated stack, and
2. `interp_program`, which interprets a list of instructions, producing the
   resulting value (which will be the last value pushed to the stack).

These functions should raise the `ShortStack` exception if there aren't enough
arguments on the stack to perform an instruction.

**Task 2.6**: In `lib/arith.ml`, implement the functions `interp_instr` and
`interp_program`.

**Task 2.7:** In `test/test_arith.ml`, write tests for the
as-of-yet-unimplemented function `compile_bin : s_exp -> instr list` that
compiles an expression into a list of instructions. If an expression cannot be
evaluated, `compile_bin` should raise the `Stuck` exception.

**Task 2.8:** In `lib/arith.ml`, implement the function `compile_bin`.

**Task 2.9:** In `test/test_arith.ml`, write tests that compare the
output of compiling and then executing (`compile_bin` followed by
`interp_program`) versus directly interpreting (`interp_bin`) on a variety of
different inputs.

### Task 3: Variadic (3 subtasks)

The `variadic` language adds support for variadic `+` and `*` operators. That
is, both operators will be callable with **any** number of arguments.

The grammar of `variadic` is as follows:

```bnf
<expr> ::= <num>
         | (+ <expr> ...)
         | (* <expr> ...)
```

where `<expr> ...` means zero or more expressions.

**Note:** Additional parentheses are _not_ allowed; e.g., `((1))` is not a valid
`variadic` program.

There are two main ways to go about adding this support:

- Extend the interpreter and compiler of the simpler language to support the
  new features.
- Translate expressions in the extended language into ones that are valid in
  the simpler one, then use the interpreter and compiler of the simpler
  language.

  **Example:** `(+ 1 2 3)` translates to `(+ 1 (+ 2 3))`.

  **Note:** This approach, which is called _desugaring_ (since it takes a
  sweet/appealing syntax and translates it to an equivalent, often less
  appealing one), is only possible if the simpler language is capable of
  expressing the same functionality as the extended one. For instance, we
  couldn't desugar a division operator into the `bin` language, since no
  combination of addition and multiplication will achieve the same result.

**Task 3.1** In `lib/arith.ml`, implement the function
`desugar_variadic : s_exp -> s_exp` that takes a `variadic` expression and
translates it into the `bin` language.

**Hint:** Note that `variadic` supports zero or one arguments for `+` and `*`.
You may assume that any missing arguments may default to the identity elements
`0` and `1`, respectively. For example `(* 4)` should evaluate to `4` and `(+)`
should evaluate to `0`.

**Task 3.2:** In `lib/arith.ml`, implement the function
`interp_variadic : s_exp -> int` that directly interprets a `variadic`
expression (i.e., **without relying on `desugar_variadic`**).

**Task 3.3:** In `test/test_arith.ml`, write tests that compare the output of
of interpreting after desugaring (`desugar_variadic` followed by `interp_bin`)
and `interp_variadic` against each other on a variety of different inputs.
