# BP-toy-resolution
Sage code to compute Ext over the BP Hopf algebroid

This is a simple Sage file that implements the BP Hopf algebroid and its bar resolution.
It can compute some siimple, low-dimensional and low-filtration Novikov Ext groups. See bpbar.pdf for some results.

To reproduce the computation you need Sage, the sagetex package and pdflatex. Just run

   pdflatex bpres.tex
   sage bpbar.sagetex.sage
   pdflatex bpres.tex
