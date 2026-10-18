---
schema: gloss/v3
target: euclid-primes
subject:
  kind: statement
  node: variant-2a7919a9
  module: null
  lean_hash: 2a7919a9cf736954b293aa118cece228b4807770042561f24d39d97ce9d7c43b
supersedes: null
author: f29-words
drafter: null
date: '2026-10-18'
licence: CC-BY-4.0
drafted_with: Claude Fable 5.1 (claude-fable-5-1)
label: No finite list contains all the primes
---
$$\forall\, l\in\operatorname{List}(\mathbb{N})\ \ \exists p\in\mathbb{N}:\quad p\ \text{prime}\ \wedge\ p\notin l$$

For every list of natural numbers there is a prime that is not a member of it (Euclid, Elements IX.20). Prime is the problem's own `Opn.IsPrime`: $2\le p$ and every $d$ with $p=d\cdot c$ for some natural $c$ is $1$ or $p$.
