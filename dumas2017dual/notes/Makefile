# Makefile for LaTeX documents

# Main document
MAIN = field_approximation

# LaTeX compiler
LATEX = pdflatex

# BibTeX compiler (if needed)
BIBTEX = bibtex

# Viewer (adjust for your system)
VIEWER = open

.PHONY: all clean view help

# Default target
all: $(MAIN).pdf

# Compile PDF (run twice for cross-references)
$(MAIN).pdf: $(MAIN).tex
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

# Compile with bibliography (if needed)
bib: $(MAIN).tex
	$(LATEX) $(MAIN).tex
	$(BIBTEX) $(MAIN)
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

# View the PDF
view: $(MAIN).pdf
	$(VIEWER) $(MAIN).pdf

# Clean auxiliary files
clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc 
	rm -f $(MAIN).bbl $(MAIN).blg $(MAIN).nav $(MAIN).snm
	rm -f *.aux *.log *.out *.toc *.bbl *.blg

# Clean everything including PDF
distclean: clean
	rm -f $(MAIN).pdf

# Help message
help:
	@echo "Available targets:"
	@echo "  all        - Compile PDF (default)"
	@echo "  bib        - Compile with bibliography"
	@echo "  view       - Open PDF in viewer"
	@echo "  clean      - Remove auxiliary files"
	@echo "  distclean  - Remove all generated files"
	@echo "  help       - Show this message"




