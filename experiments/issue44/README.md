# Issue 44 Woeginger Coverage Verification

Verification run: 2026-05-09 20:24:31 UTC

Issue 44 asks to re-check the repository against Gerhard Woeginger's live
P-versus-NP attempts list and create follow-up issues for any missing attempts.

## Commands

```bash
python3 scripts/check_attempt_structure.py --json experiments/issue44/live-attempts-report.json
python3 scripts/check_attempt_structure.py --fail-on-missing-woeginger --json experiments/issue44/fail-on-missing-report.json
python3 scripts/test_check_attempt_structure.py
python3 scripts/check_attempt_structure.py --offline --generate-list --output proofs/attempts/ATTEMPTS.md
```

## Results

| Check | Result |
| --- | ---: |
| Repository attempts scanned | 116 |
| Valid attempts with README.md | 116 |
| Complete attempts by current recommended layout | 39 |
| Partial attempts by current recommended layout | 77 |
| Attempts with legacy-layout warnings | 56 |
| Woeginger live entries parsed | 116 |
| Woeginger entries matched to repository attempts | 116 |
| Missing Woeginger entries | 0 |
| Unmatched repository attempts | 0 |
| Generated attempts index changes | 1 added row |

`--fail-on-missing-woeginger` exited successfully, so no per-entry missing
attempt issues were created.

The regenerated `proofs/attempts/ATTEMPTS.md` index adds the Craig Alan
Feinstein 2006 attempt row that is present in `proofs/attempts/`.

## Conclusion

The live Woeginger coverage condition for Issue 44 is satisfied: every parsed
entry from the live list has a repository attempt. The remaining findings are
structure-quality follow-ups: 77 attempts are partial under the recommended
`original/`, `proof/`, and `refutation/` layout, and 56 attempts still carry
legacy-layout warnings.
