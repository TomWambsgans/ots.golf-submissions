# RISC-V upper bound: 1628 cycles

A certified RV64IM verifier for a forest one-time signature: every execution, accepting or
rejecting, terminates within 1628 cycles and computes exactly the Lean verifier's oracle
computation. `Solution.lean` exports `OptimalOTS.Challenge.UpperRiscv.submission` and
`certificate` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-riscv.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-riscv.md).

## Construction

- **Scheme.** The nibble-layout forest (`ForestAlgorithm.lean`), with a complete Lean certificate
  for admissibility, 127-bit strong security and verification within 186 compressions. The index,
  the low 128 bits of `H(message ‖ nonce)`, is accepted when its 32 nibbles are at most 14 and sum
  to 166 (`Valid.lean`). Chain `k < 32` is disclosed at position `14 - nibble k`, chains 32 to 35
  at position 14 (`FixedChoice.lean`). `GScheme.lean` is the paper's graph scheme with this
  acceptance predicate; its security and graph proofs are ported from the UpperCompressions
  forest.
- **Machine image.** `CompactProgram.lean` is a 2647-instruction RV64IM image: a straight-line
  nibble sweep that checks the index and stores the chain positions; 32-byte value slots; one
  block per active chain that copies its disclosed word and jumps into a table of 14 hash steps;
  and a scratch buffer for the tree inputs. Nodes are numbered chain-major (`Names.lean`), so the
  specification's reader visits each chain in the order the blocks run.
- **Cycle count.** One cycle per executed instruction and two for the 912-bit root hash, with each
  chain block charged by the path actually taken: 267 cycles for the index phase and 973 for the
  chains on every accepted index, 1628 in the worst case.

## Proof map

| File | Content |
|---|---|
| `Wire.lean`, `WireAdapter.lean` | the OTS certificate transferred to raw signature bit strings |
| `Refines.lean` | `Riscv.Refines`: an observed oracle computation with a cycle bound |
| `CompactVerifier.lean` | `image_refines`: the image equals the certified verifier on every input, within 1628 cycles |
| `IndexChecks.lean`, `IndexRefines.lean`, `IndexInput.lean` | the index query, the nibble sweep and the input checks |
| `DecodedInput.lean`, `ExecutionContext.lean`, `InitialStorage.lean` | the state left for reconstruction: input buffers, chain positions, disclosure cursor |
| `CompactChains.lean`, `CompactLevels.lean` | the chain blocks and their cost |
| `CompactTree.lean`, `CompactSubtrees.lean`, `CompactRoot.lean` | the group, subtree, root and decision blocks |
| `TagStore.lean` | the tweak stores shared by all hash inputs |
| `SweepRefines.lean` | the generic per-node segment framework |
| `CompactBlocks.lean`, `CompactLayout.lean`, `BlockExecution.lean`, `AssemblyMacros.lean`, `CopyProof.lean`, `HashOutput.lean`, `LoaderProof.lean`, `MachineCost.lean`, `MachineMemory.lean` | machine semantics, memory layout and reusable execution rules |
| `Candidate.lean` | `machineCertificate`, bundling the OTS and machine proofs |
| `Solution.lean` | the exported declarations |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py upper-riscv --source .
```
