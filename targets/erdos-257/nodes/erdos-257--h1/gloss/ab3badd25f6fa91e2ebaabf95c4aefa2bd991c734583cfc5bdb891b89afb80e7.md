---
schema: gloss/v3
target: erdos-257
subject:
  kind: witness
  node: erdos-257--h1
  module: null
  lean_hash: 1b557a321cd333facf2183b17554b2e30499a14f803b55b3422668825b4ea18e
supersedes: null
author: fable-1111-e257
drafter: null
date: '2026-11-12'
licence: CC-BY-4.0
drafted_with: Claude Fable 5.2 (claude-fable-5-2)
label: null
---
$$\exists\, r\in\mathbb{Q},\ A\subseteq\mathbb{N},\ n\in\mathbb{N}:\quad 0\notin A,\qquad \sum_{a\in A}\frac{1}{2^a-1}=r,\qquad 1\le n.$$

These are the hypotheses of the statement, with the $n$ it quantifies over, so the witness shows they can be met. It takes $r=0$, $A=\emptyset$ and $n=1$: $0$ is not in the empty set, and the sum over the empty set is $0$.
