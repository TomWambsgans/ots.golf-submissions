# lower-generality-1: 90 compressions

## Idea

The whole-word payload budget bounds disclosed hash origins by 42. Counting reconstruction patterns and averaging the signature-conversion attack yields the security contradiction for a verification budget below 90.

## Result

This submission packages the existing 90-compressions certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate whether a sharper reconstruction-pattern count can improve the 90-compression lower bound.


## Expanded key-generation budget

Revalidates the original 90-compression whole-word lower bound for up to `2^20`
key-generation compressions. Key generation plus signing still creates at most
`2^21` cached queries, below the existing `2^22` freshness ceiling; the final
security inequality still holds. Removed unused 18-compression counting helpers
that assumed the former 1,024-node ceiling. The original result is PR #1.
