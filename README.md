# Reproduction package

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24211936.svg)](https://doi.org/10.5281/zenodo.24211936)

Code and logs for the paper **"When the Packing Fails Silently: Aggregate Binding and Packing Robustness in Multi-Type Smart-Grid Data Aggregation"**.

Every table and figure in the paper is produced by a script in `repro/`, with seeds fixed at the top of each file. Nothing here requires network access, a GPU, or a third-party cryptographic library: the pairing is implemented from scratch in `toybilinear.py` so that the reported numbers can be checked on any machine with Python 3.9+.

## Requirements

```
python 3.9+
matplotlib    # only for the two figure scripts
```

```bash
pip install -r requirements.txt
```

## Experiment scripts

Each row reproduces the artifact named in its second column. Run from inside `repro/`; each script writes a log file whose values are the ones quoted in the paper.

| Script | Produces | Runtime |
|---|---|---|
| `toybilinear.py` | Symmetric pairing and its self-test (bilinearity, non-degeneracy) | <1 s |
| `vpmda_demo.py` | Honest round; attacks A1 and A1+; the `CT^N` repair failure | 0.1 s |
| `binding_audit.py` | Table III: three ciphertext spaces × four authentication scopes | 0.1 s |
| `overflow_demo.py` | Carry threshold, silent-zone scan, check-digit detection and false positives | 0.9 s |
| `collude_demo.py` | Dilution `1+n/(2c)`, detection under prescribed check-digit computation, localization collapse, finite-sample experiment | 4.3 s |
| `lppmm_audit.py` | LPPMM-DA instantiation: honest round, arbitrary-tuple forgery, CRT wrap-around | 2.5 s |
| `param_check.py` | Proposition 2, the audit of Table VII, `T`-sensitivity, feasible frontier | 0.2 s |
| `chunk_demo.py` | Theorem 1 instance, isolation, threshold, localization, availability, overhead frontier | 3 s |
| `vpmda_full.py` | Full protocol with check digit and chunking: honest, shift, overflow, cross-domain, dropout | 17 s |
| `bscan.py` | Fig. 4 and Table VIII: threshold, localization surcharge, payload, latency, availability, censorship | 113 s |
| `check_coefficients.py` | Consistency check of the check-digit coefficients across block sizes | <1 s |

Per-script logs from the runs reported in the paper are in `logs/`.

## Figure sources

| Script | Produces |
|---|---|
| `figs_schematic.py` | Figures 1–3 (system model, the two unguarded paths, chunked packing) |
| `draw_schematic_svg.py` | Vector (SVG) versions of the same three figures |

## Notes on the numbers

- Timings are wall-clock on a single core of an ordinary laptop and are dominated by the 41-bit pairing implementation. They indicate relative cost, not performance; the paper says so explicitly and does not draw conclusions from absolute milliseconds.
- The pairing is a toy construction over a 41-bit field. It is sufficient to demonstrate that the protocol logic — packing, peeling, the check digit, the mask algebra — behaves as claimed, and insufficient for any security claim about the real parameters. The paper states this in §VIII-A.
- Monte-Carlo counts are reproducible because every seed is fixed; changing a seed changes the last digit of a percentage, not a conclusion.

## License

MIT. See `LICENSE`.
