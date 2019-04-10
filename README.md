# isabelle-zf-experiments

[![CircleCI](https://circleci.com/gh/alexkrauss/isabelle-zf-experiments.svg?style=svg)](https://circleci.com/gh/alexkrauss/isabelle-zf-experiments)

This repository contains an experimental clone of (some parts of) Isabelle/ZF, originally developed by Larry Paulson.

The goal is to experiment with type systems on top of set theory.

## Where is what?

* The basic definitions of first-order logic and set theory are in `First_Order_Logic.thy` and `Set_Theory.thy`.
* The most significant change wrt. the original is the application syntax. As in Isabelle/HOL, we use `f x y` instead of `f(x,y)`.
* `Typing.thy` bootstraps type syntax and tooling and contains some minimalistic examples.