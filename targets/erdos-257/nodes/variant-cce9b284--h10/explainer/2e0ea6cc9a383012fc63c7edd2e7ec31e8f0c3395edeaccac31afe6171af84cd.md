---
schema: explainer/v2
target: erdos-257
node: variant-cce9b284--h10
proof: 4ac9498059102fa290461fba2e7009103cf34bb809cc10734300255e172722f4
supersedes: null
author: t1125-257
drafter: null
date: '2026-11-24'
licence: CC-BY-4.0
drafted_with: Claude Opus 5.5 (claude-opus-5-5)
---
## Statement

Let $r$ be the greedy walk of $2^{-j}$: $r_0 = 2^{-j}$, and $r_{k+1} = r_k - \frac{1}{2^k-1}$ when $k \ge 1$ and $\frac{1}{2^k-1} \le r_k$ (index $k$ is *taken*), otherwise $r_{k+1} = r_k$. For $n < m$, the walk's weighted count $W_n(m) = \sum_{i\ge0} 2^{-(i+1)}\#\{a \le n \text{ taken} : a \mid m+i+1\}$ is at most $G_j(m) = \sum_{i \ge 0} 2^{-(i+1)}\#\{a : j < a < m,\ a \mid m+i+1\}$.

## The walk never takes an index at most j

Each term $\frac{1}{2^k-1}$ is nonnegative (for $k = 0$, Lean's $1/0 = 0$), so the walk never increases: $r_k \le 2^{-j}$ (`opn_walk_le`). For $1 \le a \le j$ we have $2^a - 1 < 2^j$, so $\frac{1}{2^a-1} > 2^{-j} \ge r_a$ and $a$ is not taken (`opn_small_not_taken`).

## Termwise comparison

A taken $a \le n$ dividing $m+i+1$ has $a > j$ and $a \le n < m$, so for each $i$ the set counted on the left is a subset of the set counted on the right. The right-hand sets lie in $[0, m)$, so they are finite with at most $m$ elements.

## Summing

Both series are dominated by the convergent $\sum_i 2^{-(i+1)} m$, so both are summable, and `Summable.tsum_le_tsum` gives $W_n(m) \le G_j(m)$. $\blacksquare$

This is `variant-cce9b284--h4` with $20$ replaced by a general $j$, by the same argument.
