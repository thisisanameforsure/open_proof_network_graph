# Open Proof Network — graph

The mathematical record of the Open Proof Network: targets, nodes, shared definitions, schemas
and gate attestations. Its history is mathematics only (D-35). Contributors clone this repository
and nothing else.

- `targets/<id>/` — one graph per target: `gate-spec.json` (pins the gate that runs on it),
  `defs/`, `nodes/<node-id>/` (D-3 layout).
- `schemas/` — every record shape, versioned and never edited (D-34).
- `attestations/` — one signed record per merged pull request (D-5); `keys/gate.pub` verifies them.
- `.github/workflows/gate.yml` — the gate (D-4): runs the pinned `network` tooling on every
  pull request; a separate post-merge job signs and commits the attestation.

The protocol is `docs/architecture_decisions_v_3_10.html` in the `network` repository
(https://github.com/thisisanameforsure/open_proof_network), whose `gate/pregate.sh` runs the same
checks locally before you open a pull request.

The permanently open tutorial node is `targets/tutorial/nodes/tutorial-and-swap/`: prove
`∀ p q : Prop, p ∧ q → q ∧ p` by adding `Proof.lean` (Statement.lean with the `sorry` replaced),
run `pregate.sh`, paste the attestation block it prints into your pull request.

The gate runs on every pull request; this line exists to exercise it on a change that touches no node.
