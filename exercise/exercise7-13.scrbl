#lang scribble/base

@title{Exercise 7.13}

let式の型推論の規則を書く

Γ ⊢ e1 : τ1  Γ, x : τ1 ⊢ e2 :τ2 

--------------------------------------------------------------

let x = e1 in e2 : τ2

1. no type
2. 