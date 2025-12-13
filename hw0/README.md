# Homework 0: We're *root*ing for you!

_**Note:** This is a 1-week assignment (due 1 week after release)._

## Introduction

In this homework, you'll be implementing two estimation methods, one for
computing square roots and one for computing roots of functions.

If you haven't written any OCaml before (we don't assume that you have!) it
will be useful to take a gander at chapters 1 and 2 of [Functional
Programming in OCaml](https://courses.cs.cornell.edu/cs3110/2021sp/textbook/).

Also, a heads up: this homework is going to be much more "mathy" then the rest
of the course. The purpose of Homework 0 is just to get you started writing
OCaml. After this homework, we'll use the OCaml skills you learn from this
homework to dive into a style of programming that is much more typical of
compiler construction. So, this is just a friendly note to say: don't worry
about internalizing any algebra in this homework---we just want you to start
getting friendly with OCaml!

### Software

To set up your environment for working on the homework for CS 164, please review
our [software page](https://inst.eecs.berkeley.edu/~cs164/fa25/software.html).

### Testing

For this homework (and _only_ this homework), a complete test suite is
provided---you can look at the tests in `test/test_hw0.ml`. We will use these
tests (and only these tests) to grade your solution.

### Useful commands

`dune build` builds everything.

`dune runtest -f` runs the tests in the `test/` directory.

`dune runtest --watch` continuously monitors the file system and re-runs the
test suite whenever a file is changed and saved.

`dune utop` runs a toplevel. You can access the functions you're developing for
this homework by running, e.g.:

```shell
# dune utop
utop> open Hw0;;
utop> square 4.0;;
16.0
```

(If you leave off the `open Hw0`, you'll get an error when you try to call
`square`.)

### Tip: float operations

In OCaml, the functions `+`, `-`, `*`, and `/` work only on `int`s (integers).
To perform the same operations on `float`s, use the corresponding functions
suffixed by a dot: `+.`, `-.`, `*.`, and `/.`.

## Support code

The stencil file `lib/hw0.ml` provides you with a function `close` that,
given two successive estimates, determines whether they are "close enough" to
each other for our numerical purposes. In other words, `close` will tell you
if an estimation process has _converged_.

## Tasks

### 1. Square (1 subtask)

**Task 1.1:** Implement a function `square` that takes a number and returns its
square.

### 2. Babylonian Method (2 subtasks)

The
[Babylonian Method](https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
is a method for computing square roots. Given a `guess` of the square root of a
number `n`, it estimates the error of the guess (how far _below_ the actual
square root the guess is) to be

```
(n - guess^2) / (2 * guess)
```

Denoting this error as `e`, the revised estimate produced by a step of the
Babylonian method is `guess + e`.

**Task 2.1:** Implement a function `babylonian_step` that produces a revised
estimate for the square root of `n` given a `guess`.

**Task 2.2:** Implement a function `babylonian` that produces a _close enough_
(as determined by `close`) estimate for the square root of `n` given an initial
`guess`. Your code should test successive guesses for closeness---_not_ the
closeness of guesses to the actual square root.

_Note:_ You'll need to rewrite the definition of `babylonian` to use `let rec`
because it is **rec**ursive (i.e., needs to be able to call itself).

### 3. Newton's Method (2 subtasks)

A "root" of a function `f` is a value `x` such that `f(x) = 0`; in other words,
if plotted on the plane, the roots correspond to the points where the function
crosses or touches the x-axis. (Fun fact: a "square root" of a number `n`, as
discussed in the previous exercise, is just a root of the function
`f(x) = n - x^2`!)

[Newton's Method](https://en.wikipedia.org/wiki/Newton%27s_method) is a method
for finding the roots of real-valued functions. Given a `guess` of the root of
a function `f`, it estimates the error of the guess (how far _above_ the actual
root the guess is) to be `f(guess)/f'(guess)` (where `f'` is the
derivative---that is, slope---of `f`).

Denoting this error as `e`, the revised estimate for a root of `f` produced by a
step of Newton's method is `guess - e`.

**Task 3.1:** Implement a function `newton_step` that produces a revised
estimate for the root of `f` given a definition for `f'` and a guess.

_Note:_ `f` and `f'` are functions that consume and produce `float`s, so they
are of type `float -> float`.

**Task 3.2:** Implement a function `newton` that produces a _close enough_ (as
determined by `close`) estimate for a root of `f` given a definition for `f'`
and an initial `guess`.

_Note:_ This should be really similar to `babylonian`! (You'll also need to use
`let rec` here.)
