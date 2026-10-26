---
schema: gloss/v3
target: erdos-849
subject:
  kind: statement
  node: variant-3969f1f7--h1
  module: null
  lean_hash: 3774061db8af4aff8a5d04b53d20e64f28c3fdb8e32cf8cc1e03400067b5643a
supersedes: 43401687fb006b7c9107c2e1beb152f74793a42a067e2e357f5ec06337199eb4
author: t1026e-c
drafter: null
date: '2026-10-26'
licence: CC-BY-4.0
drafted_with: Claude Opus 5.5 (claude-opus-5-5)
label: rows with bounded k
---
$$\forall K, a \in \mathbb{N}:\quad \#\bigl\{\, n \;:\; \exists k,\ 2 \le k \le K,\ 2k \le n,\ \tbinom{n}{k} = a \,\bigr\} \le K$$

The set collects **rows** $n$, each counted once; its size is `Set.ncard` ($0$ for an infinite set, though this set lies in $[0, a]$).

In words: for any $K$, at most $K$ rows of the half triangle hold $a$ at some $k$ with $2 \le k \le K$.
