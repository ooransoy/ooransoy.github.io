+++
title = "Proving Cassini's identity in Lean as a beginner's exercise"
date = 2024-03-16T19:23:31+03:00
author = "Olcay Oransoy"
description = ""

draft = true
[_build]
  list = 'never'
+++

{{< math >}}

I recently came across the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4), [the formalization of the proof of PFR](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/) over $\mathbb{F}\_2$, [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/), and a few other resources or talks about Lean, so I finally decided to get my hands dirty with it. My first idea was to check [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) to see what people have been working on. My favorite hello-world-ish thing in math is the Fibonacci numbers, so I started reading the source for [Nat.Fib](https://github.com/leanprover-community/mathlib4/blob/1a1dffdd3d023000aecf7e6940843980dcce9170/Mathlib/Data/Nat/Fib/Basic.lean#L70-L71) and noticed a few identities I know of aren't in the file. Cassini's identity, $F_{n+1}F_{n-1}-F_n^2=(-1)^n$, was the first one to come to mind, so I decided to have a go at that. (I also searched for "cassini" in the repo and the Zulip chat to see if anyone else had an implementation, but I didn't find anything noteworthy.)
## Minor difficulties
Following the [ArchWiki page on Lean](https://wiki.archlinux.org/title/Lean_Theorem_Prover#Lean_4_using_elan), I set up `elan` from the AUR with `aur sync elan-lean`, and set up Lean4 with `elan toolchain install leanprover/lean4:stable` and `elan default stable`. I also installed `lean.nvim` so that I wouldn't have to deal with VSCode.
### Importing Mathlib
I found the command to create a new project on the same page, and I started with `lake new cassini`. I tried to import `Fib` with `import Mathlib.Data.Nat.Fib`, and got the error `unknown package 'Mathlib'`. It took me a few minutes of googling to find that I should've done `lake new cassini math` on [this page](https://leanprover-community.github.io/install/project.html), so I did `cd ..; rm -r cassini; lake new cassini math; cd cassini`.
### Importing Fib
I tried `import Mathlib.Data.Nat.Fib` again, and I got
```
`/home/chromo/.elan/toolchains/leanprover--lean4---v4.7.0-rc2/bin/lake setup-file /home/chromo/code/lean/cassini/Cassini/Basic.lean Init Mathlib.Data.Nat.Fib` failed:

   stderr:
   error: 'Mathlib.Data.Nat.Fib': no such file or directory (error code: 2)
     file: ./.lake/packages/mathlib/././Mathlib/Data/Nat/Fib.lean
```
I did `cd ./.lake/packages/mathlib/././Mathlib/Data/Nat/; ls` to find that `Fib` is a folder and what I want is in `Fib/Basic.lean`, so I did `import Mathlib.Data.Nat.Fib.Basic` instead, and it worked.
### Opening the required namespace
I didn't know how to phrase the proposition in Lean, so I just wrote `theorem cassini_identity` and the Copilot completion gave `theorem cassini_identity (n : ℕ) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n :=`. With
```lean
import Mathlib.Data.Nat.Fib.Basic

theorem cassini_identity (n : ℕ) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n := by
  sorry
```
I now had the errors
```
▶ 3:36-3:47: error:
function expected at
  fib
term has type
  ?m.12

▶ 3:50-3:61: error:
function expected at
  fib
term has type
  ?m.12

▶ 3:64-3:69: error:
function expected at
  fib
term has type
  ?m.12
```
I got stuck here for some time. My google-fu turned out to be insufficient, so I searched on Zulip and found [this](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Simply.20connected.20set/near/406373816). I added `set_option autoImplicit false` and the error turned into `unknown identifier 'fib'`. At this point I was a bit confused, because I thought that in contrast to the Zulip thread I found, I _did_ have `fib` because I explicitly said `Mathlib.Data.Nat.Fib.Basic` instead of just `Mathlib` like in the thread. I had the idea of looking at the `Fib` source again, and I found a line `open List Nat` in `Fib/Zeckendorf.lean`, at which point I realized that I needed `open Nat` as well.
### Specifying an integer instead of a natural
Now I had
```
import Mathlib.Data.Nat.Fib.Basic

open Nat

theorem cassini_identity (n : ℕ) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n := by
  sorry
```
and yet another error message
```
▶ 5:77-5:79: error:
failed to synthesize instance
  Neg ℕ
```
which was pretty self-explanatory. `-1` isn't a natural, so I needed to specify that it's a $\mathbb{Z}$ and not a $\mathbb{N}$. I don't remember how I arrived at `(-1 : ℤ)`, but I remember that it didn't take me as long as the previous problem to solve.

I finally had a valid file! Now to get rid of the `declaration uses 'sorry'`.
### Some progress
I thought that the determinant proof with $$F_{n-1}F_{n+1}-F_{n}^{2}=\det \left[{\begin{matrix}F_{n+1}&F_{n}\\\\F_{n}&F_{n-1}\end{matrix}}\right]=\det \left[{\begin{matrix}1&1\\\\1&0\end{matrix}}\right]^{n}=\left(\det \left[{\begin{matrix}1&1\\\\1&0\end{matrix}}\right]\right)^{n}=(-1)^{n}$$
would be too hard to implement, so I just decided to implement the inductive proof:
$$\begin{align}
F_{n+1}F_{n-1}-F_{n}^2&=(-1)^{n}\\\\
F_{n+1}F_{n-1}+F_{n+1}F_n-F_{n}^2-F_nF_{n+1}&=(-1)^{n}\\\\
F_{n+1}(F_{n-1}+F_{n})-F_{n}(F_{n}+F_{n+1})&=(-1)^{n}\\\\
F_{n+1}^2-F_{n}F_{n+1}&=(-1)^{n}\\\\
F_{n}F_{n+1}-F_{n+1}^2&=(-1)^{n+1}
\end{align}$$
I recalled an example of an inductive proof, again, from the `Fib.Basic` source:
```lean
theorem le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n := by
  induction' five_le_n with n five_le_n IH
  ·-- 5 ≤ fib 5
    rfl
  · -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc
      n ≤ fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)
```
I noticed the `(five_le_n : 5 ≤ n)` and realized I needed something similar, as the identity had a $F_{n-1}$. Sticking to the example, I got to
```
import Mathlib.Data.Nat.Fib.Basic

open Nat

theorem cassini_identity (n : ℕ) (n_pos : 0 < n) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1 : ℤ) ^ n := by
induction' n_pos with n n_pos IH
rfl
```
giving
```
case step
n✝ n : ℕ
n_pos : Nat.le (succ 0) n
IH : ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) ^ 2 = (-1) ^ n
⊢ ↑(fib (succ n + 1)) * ↑(fib (succ n - 1)) - ↑(fib (succ n)) ^ 2 = (-1) ^ succ n
```
### Intermediate goal
I had no idea how to add $+F_{n}F_{n+1}-F_{n}F_{n+1}$ to the LHS, so I had to think for a bit. I recalled the `add_zero` from the Natural Number Game, and I thought that if I had some intermediate result that $0=F_{n}F_{n+1}-F_{n}F_{n+1}$, I could rewrite the new zero on the LHS with it. I found on [this](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#introducing-auxiliary-subgoals) page that I can create intermediate results with `have`. At this point I went to dinner, and while eating I had an idea: I could just set $F_{n+1}(F_{n-1}+F_{n})-F_{n}(F_{n}+F_{n+1})=(-1)^{n}$ as the intermediate result on its own and prove it by simplifying it to the IH. I didn't remember almost any of the arithmetic theorems, so I just found a list of basic theorems for [rings](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html) and [groups](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html), and I got to `have h1 : fib (n + 1) * (fib (n - 1) + fib n) - fib n * (fib n + fib (n + 1)) = (-1 : ℤ) ^ n := by rw [mul_add, mul_add, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]`.

Note: An interesting observation is that I didn't notice that the line was getting so long. I think this is because my focus was more on the info panel instead of the code itself.

At this point I had `⊢ ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) * ↑(fib n) + (↑(fib (n + 1)) * ↑(fib n) - ↑(fib n) * ↑(fib (n + 1))) = (-1) ^ n` as the goal. I recalled a tactic called `simp` from some random Copilot suggestion from when I was defining `cassini_identity`, so I tried that and got `simp made no progress`, even though I had two of the same term. I thought that it was probably because the factors were in the wrong order, i.e. $F_{n+1}F_n-F_nF_{n+1}$ instead of $F_{n+1}F_n-F_{n+1}F_n$. I remembered from NNG that I could rewrite a specific occurrence with `nth_rewrite`, so I added `nth_rewrite 4 [mul_comm]; simp` and it worked, giving me `⊢ ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) * ↑(fib n) = (-1) ^ n`. This is precisely the inductive hypothesis, so I tried `exact IH` and got:
```
type mismatch
  IH
has type
  ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) ^ 2 = (-1) ^ n : Prop
but is expected to have type
  ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) * ↑(fib n) = (-1) ^ n : Prop
```
It wasn't _precisely_ the inductive hypothesis, so I searched Mathlib to find `pow_two`, and I ended up with
```lean
import Mathlib.Data.Nat.Fib.Basic

open Nat Int

theorem cassini_identity (n : ℕ) (n_pos : 0 < n) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1 : ℤ) ^ n := by
induction' n_pos with n n_pos IH
rfl
have h0 : fib (n - 1) + fib n = fib (n + 1) := by rw [fib_add_one]; rw [← zero_lt_iff]; exact n_pos
have h1 : fib (n + 1) * (fib (n - 1) + fib n) - fib n * (fib n + fib (n + 1)) = (-1 : ℤ) ^ n := by rw [mul_add, mul_add, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]; nth_rewrite 4 [mul_comm]; simp; rw [← pow_two]; exact IH
```
and it worked! I'm now realizing as I write this that this is pretty unreadable, but it's what I had while I was working on it.
### Subtraction problems
I now had
```
case step
n✝ n : ℕ
n_pos : Nat.le (Nat.succ 0) n
IH : ↑(fib (n + 1)) * ↑(fib (n - 1)) - ↑(fib n) ^ 2 = (-1) ^ n
h1 : ↑(fib (n + 1)) * (↑(fib (n - 1)) + ↑(fib n)) - ↑(fib n) * (↑(fib n) + ↑(fib (n + 1))) = (-1) ^ n
⊢ ↑(fib (Nat.succ n + 1)) * ↑(fib (Nat.succ n - 1)) - ↑(fib (Nat.succ n)) ^ 2 = (-1) ^ Nat.succ n
```

I added `rw [succ_eq_add_one]; simp`, but `simp` only made `n + 1 - 1` into `n` and didn't make `n + 1 + 1` into `n + 2`. I tried `one_add_one_eq_two`, but it didn't work because I had `n + 1 + 1` which parses as `(n + 1) + 1`, not `n + (1 + 1)`. Doing `add_assoc` first did the trick.

Now I needed to get the `(↑(fib n) + ↑(fib (n + 1)))` in `h1` to be `fib (n + 2)`, so I tried `← fib_add_two` and got:
```
tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  fib ?m.8163 + fib (?m.8163 + 1)
```
I had a hunch that this was because of the up arrows, which I assumed to be typecasts from $\mathbb{N}$ to $\mathbb{Z}$, so I looked through the `Int` documentation and tried `← ofNat_add`. It worked, and next was turning `↑(fib (n - 1)) + ↑(fib n)` into `fib (n + 1)`. I would have to use `n_pos` for this, so I decided to make it an intermediate goal. I had `have h0 : fib (n - 1) + fib n = fib (n + 1) := by rw [fib_add_one]`, with `⊢ n ≠ 0`. I found `zero_lt_iff` from the documentation.

### Negation
I was almost done, I had
```
import Mathlib.Data.Nat.Fib.Basic

open Nat Int

theorem cassini_identity (n : ℕ) (n_pos : 0 < n) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1 : ℤ) ^ n := by
induction' n_pos with n n_pos IH
rfl
have h0 : fib (n - 1) + fib n = fib (n + 1) := by rw [fib_add_one]; rw [← zero_lt_iff]; exact n_pos
have h1 : fib (n + 1) * (fib (n - 1) + fib n) - fib n * (fib n + fib (n + 1)) = (-1 : ℤ) ^ n := by rw [mul_add, mul_add, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]; nth_rewrite 4 [mul_comm]; simp; rw [← pow_two]; exact IH
rw [← ofNat_add, ← ofNat_add, ← fib_add_two] at h1
rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]
simp
```
with
```
h1 : ↑(fib (n + 1)) * ↑(fib (n - 1) + fib n) - ↑(fib n) * ↑(fib (n + 2)) = (-1) ^ n
⊢ ↑(fib (n + 2)) * ↑(fib n) - ↑(fib (n + 1)) ^ 2 = (-1) ^ (n + 1)
```

I needed to negate both sides, and turn the negation into a `-1` factor, and include it in the power on the RHS. Scouring the `Group` documentation again, I found `neg_sub` and `neg_eq_neg_one_mul`, and finally finished the proof.
## End result
Here's what I ended up with:

```lean
import Mathlib.Data.Nat.Fib.Basic

open Nat Int

theorem cassini_identity (n : ℕ) (n_pos : 0 < n) : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1 : ℤ) ^ n := by
induction' n_pos with n n_pos IH
rfl
have h0 : fib (n - 1) + fib n = fib (n + 1) := by rw [fib_add_one]; rw [← zero_lt_iff]; exact n_pos
have h1 : fib (n + 1) * (fib (n - 1) + fib n) - fib n * (fib n + fib (n + 1)) = (-1 : ℤ) ^ n := by rw [mul_add, mul_add, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]; nth_rewrite 4 [mul_comm]; simp; rw [← pow_two]; exact IH
rw [← ofNat_add, ← ofNat_add, ← fib_add_two, h0] at h1
rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]
simp
rw [← neg_sub, pow_two]
nth_rewrite 2 [mul_comm]
rw [h1, neg_eq_neg_one_mul, pow_succ]
```

Seeing the `▶ goals accomplished 🎉` was pretty satisfying, but my code itself on the other hand, was not. I thought that there's probably a much less verbose way of doing this (that isn't just throwing together what I learnt from the NNG and whatever I happened to find in the documentation), so I [posted it](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Feedback.20for.20a.20proof.20of.20Cassini's.20identity) on the Zulip chat for feedback.

Unsurprisingly, I have a long way to go, since Kevin Buzzard gave this proof:
```lean
theorem cassini_identity (m : ℕ) :
    fib (m + 2) * fib m - fib (m + 1) ^ 2 = (-1 : ℤ) ^ (m + 1) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_eq_add_one, pow_add, pow_one]
    repeat rw [fib_add_two] at *
    push_cast at *
    polyrith
```

_[appropriate spongebob sound effect]_

<audio controls src="/spongebob_end.wav" />

## Reflection
TODO
## Next steps
TODO
