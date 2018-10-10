FILENAME=zonal

all: 
	pdflatex -halt-on-error ${FILENAME}.tex
#	bibtex ${FILENAME}
#	pdflatex ${FILENAME}.tex
# From here the relevant information starts
	@echo '****************************************************************************************************'
	@pdflatex ${FILENAME}.tex
# if grep does not find a single line matching the pattern it exits with status 1, causing make to stop.
#   The following workaround using cat avoids this behaviour.
#	@grep Warning ${FILENAME}.blg | cat
	@make clean

clean:
# delete temporary files...
# ... related to LaTeX in general 
	@rm -f ${FILENAME}.dvi ${FILENAME}.aux ${FILENAME}.log ${FILENAME}.tex~ ${FILENAME}.toc ${FILENAME}.out 
# ... related to bibtex
	@rm -f ${FILENAME}.bbl ${FILENAME}.blg
