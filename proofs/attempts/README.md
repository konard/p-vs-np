# P vs NP Proof Attempts - Formal Verification

This directory contains analyses and partial formalizations of historical P vs NP proof attempts from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm).

**Assurance status: historical sketches.** The [coverage index](COMMON_ERRORS.md#attempt-coverage-index) assigns each folder an evidence level. Only 2 of the 116 folders have a mechanized concrete refutation: [sergey-gubin-2010-peqnp](sergey-gubin-2010-peqnp/) and [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/). 2 more have conditional results (anatoly-plotnikov-2007-peqnp, matt-groff-2011-peqnp), 1 has an identified gap (author104-2015-peqnp), and 111 are informal or unverified analyses. For example, the Ted Swart folder is an informal analysis; the published refutation of Swart's approach is Yannakakis' theorem on symmetric LP formulations (STOC 1988; JCSS 1991). Formal files here can compile with admissions or unproved axioms. A `refutation/` directory documents an analysis, not an automatically certified conclusion. Only the named results in [the certified-result manifest](../../scripts/proof_status.json) receive the separate assumption audit.

## Purpose

The goal is to formally verify each published P vs NP proof attempt to:

1. **Learning from errors**: Record where incorrect proofs fail, so the errors are not repeated
2. **Find the Error**: Identify exactly where each proof fails
3. **Build Expertise**: Develop formal verification skills for complexity theory
4. **Comprehensive Coverage**: Test all known attempts systematically

## Structure

Each attempt has its own folder: `{author-slug}-{year}-{claim}/`

For example:
- `ted-swart-1986-87-peqnp/` - Ted Swart's 1986 P=NP attempt
- `deolalikar-2010-pneqnp/` - Vinay Deolalikar's 2010 P≠NP attempt

### Folder Contents

Two layouts are in use. The preferred layout, used by 59 folders, is described in [CONTRIBUTING.md](../../CONTRIBUTING.md):

```
attempt-folder/
├── README.md          # Description of the attempt and known errors
├── original/          # Original paper and reconstruction (present in 20 folders)
├── proof/             # Forward formalization following the author's argument
│   ├── lean/
│   └── rocq/
└── refutation/        # Formalization or analysis of why the argument fails
    ├── lean/
    └── rocq/
```

The legacy layout, used by 56 folders, has `lean/` and `rocq/` directly inside the attempt folder. One folder (figueroa-2016-pneqnp) has only `refutation/`. A `refutation/` directory alone does not mean that a refutation is proved; see the evidence level in the coverage index.

> **Note:** Isabelle/HOL support has been sunset. Existing Isabelle proofs are archived in [`../../archive/isabelle/`](../../archive/isabelle/) for reference.

## Attempts Catalog

There are **116 attempt folders** cataloged from Woeginger's list ([ATTEMPTS.md](ATTEMPTS.md)):

- **63** claiming P = NP
- **50** claiming P ≠ NP
- **3** claiming that P vs NP is unprovable or undecidable (marked ? in ATTEMPTS.md)
- Spanning from **1986 to 2016**

Woeginger's page has not been updated since 2016, and Woeginger died in 2022, so this catalog ends in 2016. Claimed proofs from 2017 to 2026 are tracked as a backlog in [literature/CLAIMED_PROOFS_2017_2026.md](../../literature/CLAIMED_PROOFS_2017_2026.md).

### Full List

The complete list is in [ATTEMPTS.md](ATTEMPTS.md). The source is [Woeginger's P vs NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm). Recurring errors are grouped in [COMMON_ERRORS.md](COMMON_ERRORS.md). The order of refutation work, the first 20 attempts and the definition of done are in [REFUTATION_PLAN.md](REFUTATION_PLAN.md).

### Issue Tracking

Each attempt has a corresponding GitHub issue as a sub-issue of [#44](https://github.com/konard/p-vs-np/issues/44). Issues were created using the `gh` CLI tool directly.

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

1. Create the preferred folder structure as shown above (see [CONTRIBUTING.md](../../CONTRIBUTING.md))
2. Add a descriptive README.md
3. Start formalizing in at least one proof assistant
4. Document any errors found
5. Link to the original paper if available

## See Also

- [Parent issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue #45](https://github.com/konard/p-vs-np/issues/45) - Create issues for all attempts
- [Main README](../../README.md) - Repository overview

---

*Last updated: 2026-11-03*
*Total attempt folders: 116 (63 P = NP, 50 P ≠ NP, 3 other)*
