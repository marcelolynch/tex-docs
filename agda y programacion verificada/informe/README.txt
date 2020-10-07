Para compilar como literate agda:
 
1) Correr bibtex:
  $ bibtex informe.lagda

2) Compilar el literate agda a .tex:
  $ aga --latex --latex.dir=. informe.lagda.tex

3) Correr pdflatex dos veces:
  $ pdflatex -synctex=1 -interaction=nonstopmode -file-line-error -jobname=informe.lagda ./informe.tex
  $ pdflatex -synctex=1 -interaction=nonstopmode -file-line-error -jobname=informe.lagda ./informe.tex
