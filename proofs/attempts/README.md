# P vs NP Proof Attempts - Formal Verification

This directory contains formal verifications of historical P vs NP proof attempts from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm).

## Purpose

The goal is to formally verify each published P vs NP proof attempt to:

1. **Educational Value**: Learn from mistakes by formalizing incorrect proofs
2. **Find the Error**: Identify exactly where each proof fails
3. **Build Expertise**: Develop formal verification skills for complexity theory
4. **Comprehensive Coverage**: Test all known attempts systematically

## Structure

Each attempt has its own folder: `{author-slug}-{year}-{claim}/`

For example:
- `swart-1986-peqnp/` - Ted Swart's 1986 P=NP attempt
- `deolalikar-2010-pneqnp/` - Vinay Deolalikar's 2010 P≠NP attempt

### Folder Contents

Each attempt folder contains:

```
attempt-folder/
├── README.md          # Description of the attempt and known errors
├── coq/              # Coq formalization
│   └── *.v
├── lean/             # Lean 4 formalization
│   └── *.lean
└── isabelle/         # Isabelle/HOL formalization
    └── *.thy
```

## Attempts Catalog

There are **111 P vs NP proof attempts** cataloged from Woeginger's list:

- **61 attempts** claiming P = NP
- **50 attempts** claiming P ≠ NP
- Spanning from **1986 to 2016**

### Full List

The complete list of attempts is available in:
- Raw JSON data: `experiments/pvsnp_attempts.json` (not committed to repo)
- Parsing script: `experiments/parse_pvsnp_attempts_v3.py`

### Creating Issues

Each attempt should have a corresponding GitHub issue as a sub-issue of [#44](https://github.com/konard/p-vs-np/issues/44).

To create issues for all attempts, use:

```bash
python3 experiments/create_attempt_issues.py
```

**Note**: This creates 111 issues. Make sure you're ready before running with option 3!

## Verification Approach

For each attempt:

1. **Read the paper**: Understand the claimed proof
2. **Identify key claims**: Extract main lemmas and theorems
3. **Formalize in stages**:
   - Start with basic definitions
   - Formalize each step of the argument
   - Continue until you hit an error or unjustified assumption
4. **Document the error**: In README.md, explain:
   - What the author claimed
   - Where the formalization breaks down
   - Why the proof is incorrect

## Source

All attempts are from Gerhard J. Woeginger's comprehensive list:
**https://wscor.win.tue.nl/woeginger/P-versus-NP.htm**

## Contributing

When adding a new attempt formalization:

1. Create the folder structure as shown above
2. Add a descriptive README.md
3. Start formalizing in at least one proof assistant
4. Document any errors found
5. Link to the original paper if available

## See Also

- [Parent issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue #45](https://github.com/konard/p-vs-np/issues/45) - Create issues for all attempts
- [Main README](../../README.md) - Repository overview

---

*Last updated: 2025-10-17*
*Total attempts cataloged: 111*
