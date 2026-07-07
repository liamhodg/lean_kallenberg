# Kallenberg in Lean

An implementation of Olav Kallenberg's "Foundations of Modern Probability (3rd Edition)" in Lean.

Probability theory is blessed to have a large number of high-quality textbooks to ease into the subject. Billingsley's classic texts are a staple for students learning about how the principles of measure theory give rise to the beauty of the central limit theorem, for exapmle.

Kallenberg's Foundations of Modern Probability is a different beast. Comprising almost 1000 pages, it is arguably the quintessential foundational probability theory reference. It contains general versions of all of the important theorems. To know Kallenberg is to understand probability theory, not in its entirety, but well enough to do meaningful work. Consequently, implementing Kallenberg in Lean should formalise the vast majority of probability theory needed for applied probabilists.

## Leanstral PNG workflow

Prepare a page before sending it to Leanstral:

```bash
python3 scripts/prepare_leanstral_page.py text/kallenberg_pg-015.png
```

The script creates:

- a Lean target under `Kallenberg/Generated/PageNNN.lean`;
- a Leanstral task prompt under `.leanstral/tasks/kallenberg_pg-NNN.md`;
- an import from `Kallenberg/Generated.lean`, so generated pages are part of the project.

Then point Leanstral at the generated task file and the PNG. Leanstral should replace the page stub with OCR-derived declarations, using `sorry` whenever the exact proof is not clear.
