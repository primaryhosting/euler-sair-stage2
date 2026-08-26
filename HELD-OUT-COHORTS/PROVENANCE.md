# Provenance — held-out exclusion index

`released_index.json` sha256 `92059bced914e39637adf79eb9d8225a1435b4eeed12e997e4e39368b6a41d27` · built 2026-08-26 (UTC date).

## Source files (byte-identical to the official released sets — see confirmation below)

| file | lines | bytes | sha256 |
|---|---|---|---|
| `evaluation_normal.jsonl` | 200 | 39967 | `6adce171b97c247196cd92cab48f59f7751bca18e1d666ede9bf7cb9da538c44` |
| `evaluation_hard.jsonl` | 200 | 39116 | `5dcef7a57e3a6500247b92bd671d60032f6fe0d397d5388b85f4ebf4d9288213` |
| `evaluation_extra_hard.jsonl` | 200 | 41454 | `53c0221ef12538ffb4ea9e55d63b6db91c002cbb24fefd8fba31eaacda2bcdf8` |
| `evaluation_order5.jsonl` | 200 | 45522 | `040016d463efdff41625bffda2c4bfbba0caa093fa5936b42c232ccf1ab104f2` |

## How the index was built
```
released_pairs = { (eq1_id, eq2_id) : record in any of the four files }   # 800
released_hyps  = { eq1_id          : record in any of the four files }    # 497
```
Re-derivable: `python3 build_released_index.py` (same four files → same index → same sha256).

## Honest scope of the exclusion claim
The held-out cohorts are held out by construction from these exact 800 rows, and
those 800 rows are **byte-identical to every official released evaluation set**
(confirmed below, 2026-08-26). The stronger phrasing "held out from every official
released set" therefore holds. The remaining boundary — private-set accuracy — is
unmeasurable before an organizer run and is *not* claimed.

## Official-source confirmation (2026-08-26)

The four source files are **byte-identical (SHA-256) to the official release**:

- Dataset: `SAIRfoundation/equational-theories-selected-problems` (HuggingFace)
- Revision: `8050c0c7563c58ab71f9210004133860c87de970` · lastModified 2026-04-28
- Files: `data/evaluation_{normal,hard,extra_hard,order5}.jsonl`
- Result: **all 4 IDENTICAL** to our frozen copies (hashes above).

The exclusion claim is therefore upgraded from “our frozen dev corpus” to **held out from every official released evaluation pair**. Re-verify:
```bash
for f in evaluation_normal evaluation_hard evaluation_extra_hard evaluation_order5; do
  curl -sL "https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems/resolve/8050c0c7563c58ab71f9210004133860c87de970/data/$f.jsonl" | shasum -a 256
done  # compare against the per-file hashes in the table above
```
