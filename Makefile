AGDA := agda
AGDA_FLAGS := --html --html-highlight=auto --highlight-occurrences

PANDOC := pandoc
PANDOC_FLAGS := --standalone

html/UCC.html:

html/%.md: %.lagda.md
	$(AGDA) $(AGDA_FLAGS) $<

html/%.html: html/%.md
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<