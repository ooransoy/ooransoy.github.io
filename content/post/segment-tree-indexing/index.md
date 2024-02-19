+++
title = "Why I think `>>1|1` belongs in a segment tree and `*2+1` doesn't"
date = 2024-02-18T16:48:13+03:00
author = "Olcay Oransoy"
type = "post"

description = "This is a draft."
draft = true
[_build]
  list = 'never'
+++

<!--more-->

{{< math >}}

Say you have a program that takes 4 boolean parameters in the form of an integer `f`, where the first four bits of `f` are the parameters of the program. You want to modify the program to execute a special case when only the first and fourth parameters are on. Is it better to write `if (f == 9) specialLogic()` or `if (f == 0b1001) specialLogic()`?

I'm pretty sure most of us would opt to write `0b1001`. It is graphically clear that only the first and last parameters are on, whereas with `9` whoever reads the code would have to think about the binary representation of the integer $9$ in order to understand when the condition is true. Conversely, if `f` were to be the count of a particular thing and we had a special case for there being nine of those things, writing `if (f == 0b1001)` would require to reader to parse `0b1001` into `9`, making `if (f == 9)` the better option.

This means that depending on the context, two different expressions that evaluate to the same thing may differ in quality (?). However, this analysis provides no insight into the difference between `9` and `0b1001` on their own, without the backdrop of a purpose and a program carrying it out.
## Base
Comparing `9` and `0b1001`, it is readily apparent that the first expression is in decimal, base 10, and the second is in binary, base 2. The second difference is that there is a `0b` at the beginning of the second expression, indicating that it is a binary literal. The first expression does not have such an indicator, as we as humanity have agreed on decimal as the _default_ way to express integers. We don't need to write `0d9`, we just write `9`.

Let's try to examine the common thing that these two expressions mean, decoupled from expressions in a certain base. To do this, let's examine the integers.
## Integers
Considering the different constructions of integers, it is apparent that integers are fundamentally objects regarding _count_. For the sake of simplicity, let's omit the negative integers and consider only the naturals.
### The successor function of the Peano axioms
The Peano axioms define the naturals by defining $0$ to be a natural, and defining $S:\mathbb{N}\to\mathbb{N}$ to be an injective function that doesn't contain $0$ in its image. This construction gives an infinite amount of naturals, where we have $0$, $S(0)$, $S(S(0))$, $S(S(S(0)))$, and so on. Then we decide to name these $0,1,2,3$. In this case, a natural corresponds to a particular number of applications of $S$ to $0$.
### Church numerals in untyped lambda calculus
The Church numerals are a way of constructing the naturals in lambda calculus where $0$ is $\lambda f.\lambda x.x$ and $S$ is $\lambda n.\lambda f.\lambda x.f(nfx)$. This gives us $1=\lambda f.\lambda x.fx$, $2=\lambda f.\lambda x.f(fx)$, $3=\lambda f.\lambda x.f(f(fx))$, and so on. Now, a natural corresponds to a function that applies its first argument to its second argument a particular number of times.
### The intersection of all rings of characteristic 0
Ignoring the complicated title, we can construct the naturals by repeatedly adding the multiplicative identity to the additive identity, so we have $2=0+1+1$, $3=0+1+1+1$, $4=0+1+1+1+1$, and so on.
# TODO rest
