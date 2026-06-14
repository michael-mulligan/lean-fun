# lean-fun

Lean 4 formalization accompanying the paper [*Compression is all you need: Modeling Mathematics*](https://arxiv.org/abs/2603.20396) (Aksenov, Bodnia, Freedman, Mulligan). It formalizes the Fibonacci-macro expansion theorem for the free abelian monoid $A_1 = \mathbb{N}$.

## The theorem

With the single generator $G = \lbrace 1 \rbrace$ and the macro set of odd-indexed Fibonacci numbers

$$M = \lbrace \mathrm{Fib}_{2j+1} : j \ge 1 \rbrace = \lbrace 2, 5, 13, 34, \ldots \rbrace,$$

write $G' = G \cup M$. The expansion function $f_{G'}(s)$ — the largest $r$ such that every element of $G$-length $\le r$ is a sum of at most $s$ generators from $G'$ — satisfies

$$f_{G'}(s) = \mathrm{Fib}_{2s+2} - 1 \qquad (s \ge 0),$$

hence $f_{G'}(s) = \Theta(\varphi^{2s})$ with $\varphi = (1+\sqrt5)/2$: a logarithmic-growth macro set giving exponential expansion.

## In Lean

`Fibonacci.lean` proves this as `fib_expansion`, stated as the two containments that pin the radius exactly:

```lean
theorem fib_expansion (s : ℕ) :
    (abelian.Ball (Nat.fib (2 * s + 2) - 1) (abelian.A 1)
       ⊆ abelian.Ball s (fibMacros ∪ abelian.A 1))
  ∧ (¬ (abelian.Ball (Nat.fib (2 * s + 2)) (abelian.A 1)
       ⊆ abelian.Ball s (fibMacros ∪ abelian.A 1)))
```

Here `abelian.A 1` is the generator set, `fibMacros` is $\lbrace \mathrm{Fib}_{2j+1} : j \ge 1 \rbrace$, and `abelian.Ball s G` is the set of elements expressible as a sum of at most `s` elements of `G`. The lower containment is coverage; the upper non-containment is the matching gap at $\mathrm{Fib}_{2s+2}$. Only the expansion result is formalized here — the wrapped-length and depth claims in the paper's statement are proved by hand there.

## Building

The proof checks against [Mathlib](https://github.com/leanprover-community/mathlib4); `Fibonacci.lean` opens with `import Mathlib`. Drop it into a Lean 4 + Mathlib project to build.
