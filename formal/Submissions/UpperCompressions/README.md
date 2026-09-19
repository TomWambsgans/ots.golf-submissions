# Upper bound: 106 compressions

An admissible, 127-bit strongly secure one-time signature whose verification costs at most 106
compressions on every input and oracle-answer path. `Solution.lean` exports `scheme`,
`admissible`, `secure` and `cost` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-compressions.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-compressions.md).

## Construction

The 63-chain forest of Section 7 of the paper, wrapped as a generic oracle algorithm:

- **Graph.** 2,795 nodes: 63 hash chains of length 14, grouped three by three into 21 group
  digests, then 7 subtree digests and one root.
- **Separation.** Every hash input starts with an explicit 16-bit tweak naming its node, charged
  in the input's full length: 144, 400 or 912 bits.
- **Key generation** costs 912 compressions.
- **Signing** tries at most `2^20` distinct nonces; a signature carries a 128-bit nonce and at
  most 5,248 disclosed bits. Availability is proved with failure at most `2^-256`.
- **Verification** hashes the 384-bit message-and-nonce input, then reconstructs the selected cut
  within 105 further compressions: `1 + 105 = 106`.

## Proof map

| File | Content |
|---|---|
| `Adapter.lean` | a DAG scheme as a generic oracle algorithm; injective serialization; equal security experiments |
| `AlgorithmCosts.lean`, `Resources.lean` | pathwise costs, wire size and rejection of oversized signatures |
| `KeygenSupport.lean`, `Correctness.lean` | cache consistency and perfect correctness of the adapter |
| `Deterministic.lean` | verification makes only hash queries |
| `Availability.lean` | fresh index queries and the repeated-failure bound |
| `Main.lean` and the modules it imports | the forest and its strong-security proof (`Pr[forge] ≤ (B - 912) / 2^127`) |
| `ForestAlgorithm.lean` | admissibility, security and cost of the wrapped scheme |
| `Solution.lean` | the exported declarations |

The security proof's architecture is described in
[upper-bound-proof.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-bound-proof.md).

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```
