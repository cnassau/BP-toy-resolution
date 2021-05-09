# BP toy resolutions

Sage code to compute Ext over the BP Hopf algebroid

This is a simple [Sage](https://www.sagemath.org/) file that implements the BP Hopf algebroid and its bar resolution.
It can compute some low-dimensional and low-filtration Novikov Ext groups. See [bpbar.pdf](bpbar.pdf) for some results.

To reproduce the computation you need Sage, the sagetex package and pdflatex. Just run

```bash
   pdflatex bpres.tex
   sage bpbar.sagetex.sage
   pdflatex bpres.tex
```
