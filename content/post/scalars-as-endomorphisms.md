+++
title = 'Defining a vector space with a single statement using algebra'
date = 2024-02-24T11:32:32+03:00
author = "Olcay Oransoy"
description = "I accept the offer made to me by the devil to give up geometry."
+++

{{< math >}}

I learnt of this idea 2 days ago while I was chatting with the MATH201 TA after a recitation<s>, complaining about the absurdity of the course showing matrices before linear transformations</s>. 

TL;DR: Given an abelian group $V$ and a field $F$, if we can find a ring homomorphism $\phi:F\to\mathrm{End}(V)$, then $V$ forms a vector space over $F$ when we define $av:=\phi(a)(v)$.

Note: Everything mentioned here works for modules as well as vector spaces by just substituting a ring for the field.

---

# The main idea
Let $V$ be a vector space over a field $F$ and let $u,v,w\in V$.

Consider what a scalar does. By the vector space axioms, scaling preserves the structure of the vector space, so if $u+v=w$ then $au+av=aw$ for all $\alpha\in F$. Because of this structure preservation, considering our vector space as an abelian group, this scaling operation is just an endomorphism on that group. So, every fixed $\alpha\in F$ would correspond to $\phi_\alpha:V\to V$ where $\phi_\alpha(v)=\alpha v$.

Conversely, $\phi_\alpha$ _being an endomorphism would imply_ $\alpha u+\alpha v$ _without requiring $V$ to be a vector space in the first place_.

Obviously, the structure of scalars don't only appear as the homomorphism property, they appear in the context of other scalars as well. I am of course talking about $\alpha(\beta v)=(\alpha\beta)v$ and $(\alpha+\beta)v=\alpha v+\beta v$ for $\alpha,\beta\in F$. Translating this to endomorphisms, we have $\phi_\alpha(\phi_\beta(v))=(\phi_\alpha\phi_\beta)(v)$ and $(\phi_\alpha+\phi_\beta)(v)=\phi_\alpha(v)+\phi_\beta(v)$.

The above suggests that multiplication of endomorphisms be defined as composition and addition be defined as pointwise addition. This is precisely the structure of $\mathrm{End}(V)$, the endomorphism ring of $V$!

All of the structure we define a vector space to have is already present in its endomorphism ring. This means that the only thing we have to do is map the field elements to the endomomorphisms in a way that preserves the desirable structure of the endomorphism ring. So we're looking for a structure-preserving map, which is precisely a homomorphism!

In light of this, we can see that at the core of the vector space is a homomorphism $\phi:F\to\mathrm{End}(V)$, where $\alpha v=\phi(\alpha)(v)$ for all $\alpha\in F$ and $v\in V$.

---

# Defining the vector space
## Standard definition
Fraleigh's _A first course in abstract algebra_ defines a vector space over a field $F$ as an additive abelian group $V$ equipped with an operation of scalar multiplication satisfying the following properties for $u,v\in V$ and $\alpha,\beta\in F$:
1. $\alpha v\in V$
2. $\alpha(\beta v)=(\alpha\beta)v$
3. $(\alpha+b)v=\alpha v+bv$
4. $\alpha (u+v)=\alpha u+\alpha v$
5. $1v=v$ where $1$ is the multiplicative identity of $F$.
## Applying the idea
Let $V$ be an abelian group, $F$ a field, and $\phi:F\to\mathrm{End}(V)$ be a ring homomorphism from $F$ to the endomorphism ring of $V$. We claim that defining $\alpha v:=\phi(\alpha )(v)$ for $\alpha \in F$ and $v\in V$ makes $V$ a vector space over $F$.

> $\alpha v\in V$

$\phi(\alpha )$ is an endomorphism of $V$, so $\alpha v\in V$.

> $(\alpha\beta)v=\alpha(\beta v)$

$(\alpha\beta)v=\phi(\alpha\beta)(v)=(\phi(\alpha)\circ\phi(\beta))(v)=\phi(\alpha)(\phi(\beta)(v))=\phi(\alpha)(\beta v)=\alpha(\beta v)$. Here, $\phi(\alpha \beta)(v)=(\phi(\alpha )\circ \phi(\beta))(v)$ is because multiplication in $\mathrm{End}(V)$ is defined as composition.

> $(\alpha+\beta)v=\alpha v+\beta v$

$(\alpha+\beta )v=\phi(\alpha+\beta )(v)=(\phi(\alpha)+\phi(\beta ))(v)=\phi(\alpha)v+\phi(\beta )v=\alpha v+\beta v$.

> $\alpha(u+v)=\alpha u+\alpha v$

$\phi(\alpha)(u+v)=\phi(\alpha)(u)+\phi(\alpha)(v)=\alpha u+\alpha v$.

> $1v=v$ where $1$ is the multiplicative identity of $F$

$1v=\phi(1)(v)=\iota(v)=v$ where $\iota$ is the multiplicative identity of $\mathrm{End}(V)$ (the identity endomorphism). We use the definition of ring homomorphism in which multiplicative identity is preseved.

---

And we are done. In order to show that these two definitions are equivalent it remains to prove that the standard definition implies this algebraic definition, which is trivial.
