---
name: zooming-on-a-formula
description: When the Read rendering of an LRM page leaves a symbol ambiguous (⊨ against ⊭, a subscript, a bar), rasterize a crop of the page with pdftoppm at 250-300 dpi and Read the PNG
metadata:
  type: feedback
---

# Zooming on a formula

When a formula on an LRM page is not legible in the `Read` rendering, do not
guess from context: rasterize a crop of the physical page with
`pdftoppm -f <page> -l <page> -r 300 -x <px> -y <px> -W <px> -H <px> -png ~/IEEE\ 1800-2023.pdf <stem>`
into the scratchpad and `Read` the PNG. `pdftoppm` is at
`/opt/homebrew/bin/pdftoppm`; PyMuPDF is not installed.

**Why:** the page rendering can blur a single stroke: §F.5.3.3's abort rule,
`x ⊥^ω ⊨ P or x T^ω ⊭ P` at 300 dpi, reads as ⊭ on both completions, and a
misread glyph goes straight into the model and every test built on it.

**How to apply:** whenever a modelling decision turns on one glyph, zoom
before writing the test; a crop of a few hundred pixels is a small image.
See [[reading-the-lrm-one-page-per-call]] and [[locating-a-clause]].
