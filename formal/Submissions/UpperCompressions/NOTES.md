# Candidate 91: equal-cost chain-18 cuts with collision-aware replay

This root claims a worst-case verification bound of 91 compressions for the
generic upper-bound track. It exports the canonical raw bit-string scheme,
including deterministic verification, oversized-input rejection, admissibility,
and 127-bit strong security.

## Construction

The DAG consists of:

- 66 chains, each with 18 one-compression steps;
- 18 lower ternary hashes over the first 54 chain ends;
- 10 upper ternary hashes;
- one ten-input root hash costing three compressions.

Eight upper nodes have two lower children and one direct chain. The remaining
two have one lower child and two direct chains. All disclosed graph values are
129 bits; the public key is the low 128 bits of the root output.

Key generation costs

`66 * 18 + 18 + 10 + 3 = 1219`

compressions.

A structural mode `(a,b,g)` expands `a` of the eight first-kind upper nodes,
`b` of the two second-kind upper nodes, and `g` available lower nodes. It has

- `a + b + g` expanded ternary nodes;
- `10 + 2*(a+b+g)` disclosed words;
- `a + 2*b + 3*g` active chains;
- fixed reconstruction cost `3 + a + b + g`.

The active chain positions are chosen so their remaining lengths sum to

`87 - (a+b+g)`.

Consequently every supported cut has exact graph reconstruction cost 90, and
the constraint `a+b+g <= 16` limits disclosure to 42 words.

The contribution of a mode is

`choose(8,a) * choose(2,b) * choose(2*a+b,g)
  * comp(a+2*b+3*g, 87-(a+b+g))`.

Summing all valid modes gives exactly

`676013856769711926075368867014708`

distinct cuts. Distinct scheduled classes are mapped injectively to this
family.

## Signature and verification cost

A signature contains an 86-bit nonce and at most 42 disclosed 129-bit values:

`86 + 42 * 129 = 5504` bits.

Verification reconstructs the selected cut in 90 compressions. Its
256-bit-message/86-bit-nonce query has length 342 and costs one compression,
so the worst-case total is 91 on arbitrary raw inputs and oracle-answer paths.

## Exact 160-tier schedule

`CompactSchedule91.lean` contains literal lists of 160 class populations,
160 per-class alias multiplicities, and 160 upward-rounded winner-kernel
numerators.

The class populations sum to the exact cut-family cardinality above. They run
from

- tier 0: `165731999761240428825280379636982` classes;
- tier 159: `6273147585895` classes.

The per-class alias multiplicities are strictly increasing, from

- tier 0: `374796160129614344588800418032272040264`;
- tier 159:
  `9901842140742959321105762597502091375939212910554127043776`.

The multiplicity-weighted total is exactly

`9938514739378411853906048441678916651529596919925356639434040636883783447`

accepted 256-bit answers. The decoder identifies this accepted prefix with the
schedule's alias type and proves every class and tier fiber exactly.

Signing performs `L = 2^20` 86-bit nonce trials with replacement and retains
the earliest occurrence in the minimum accepted tier. The certificate scales
kernel witnesses by `2^80`; twenty outward-rounded squarings at `2^512`
precision bound the true first-minimum kernels.

The checked schedule envelopes include

- reference mean `< (967/1000) * κ`;
- kernel maximum `< (4/5) * L`;
- per-class winner weight `< (17/40) * L * κ`;
- diagonal term `< (13/40) * L^2 * κ`;
- post-sign positive part `< 47/100`;

where `κ = 2^-127`.

Nonce reuse is included in the availability calculation. The resulting honest
signing failure is at most `2^-129`, within the required `2^-128` bound.

## Authentication and actual-cache security

Every supported cut has equal reconstruction cost. Two distinct cuts are
therefore incomparable in the required direction: reconstruction from the
forged cut evaluates a value disclosed by the signed cut. Following the hash
immediately above that value produces either a hidden-key cache hit or a
binding discrepancy. This supplies the concrete cross-cut authentication
event.

The replay proof keeps the actual shared memoized cache. It separately tracks

- all exposed 342-bit index inputs;
- the selected message's 86-bit nonce row;
- repeated decodings of the same class;
- paid non-index queries;
- the post-sign remaining budget.

For each message row, the good event has 162 coordinates: 160 prefix deficits,
the reference score, and the literal post-sign excess score. Direct Freedman
bounds give a simultaneous empirical failure at most `2^-512`. Completion of
all message rows contributes at most `2^-760`, and the simultaneous class
occupancy cap fails with probability at most `2^-334`.

For `B <= 2^86/64`, stopped first and second moments give the coefficient

`6235189 / 6272000`.

For `2^86/64 <= B <= 2^127`, an equality-collision martingale, global diagonal
clock, and occupancy cap give four `2^-244` tails plus the `2^-334` occupancy
tail and coefficient

`2423 / 2450`.

Both coefficients are strictly below one. Above `2^127`, the universal
probability bound closes the security inequality directly.

## What required care

Treating the `2^20` nonce draws as fresh would be unsound: duplicate nonces
reuse the same memoized answer. Availability explicitly includes the
`L / 2^86` collision term, and the security proof retains private nonwinning
queries and charges their later public exposure.

A `1/100` allowance for the completed-row excess does not close the large
scalar inequality:

`1/2 + (99/98)*(48/100) > (99/98)*(968/1000)`.

The final proof controls the excess score directly at `1/1000`, producing the
`471/1000` completed-row bound.

The completion-table good event cannot be assumed pointwise after an adaptive
transcript. Its failure is averaged through the actual preceding computation.

## Validation

Run from the repository root:

`python3 .contract/verifier/verify.py upper-compressions --source .`

The exported endpoint and each newly introduced proof layer were also compiled
with Lean 4.33.1 while developing this submission. Public verified status
begins only with the hosted durable verdict.

## What to try next

The smaller numerical margin is the small-budget coefficient
`6235189/6272000`. Possible gains are a tighter stopped factor than `65/64`, a
smaller empirical multiplier than `99/98`, or a schedule with a lower reference
mean while preserving the collision moments.

A 90-compression candidate would need graph reconstruction cost 89 after
reserving the index compression. The present schedule consumes the exact
supported-family cardinality, so that step likely requires joint optimization
of the frontier modes and tier schedule while retaining an authentication
argument as strong as the equal-cost cross-cut lemma.
