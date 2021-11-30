AGDA := agda
AGDA_FLAGS := --html --html-highlight=auto --highlight-occurrences

PANDOC := pandoc
PANDOC_FLAGS := \
	--to=html5 \
	--standalone \
	--section-divs \
	--katex \
	--css=pandoc.css \
	--css=style.css

FONTS_SRC := $(wildcard fonts/*.otf)
FONTS_DST := $(foreach font,$(FONTS_SRC),html/fonts/$(notdir $(font)))

STYLES_SRC := $(wildcard *.css)
STYLES_DST := $(foreach style,$(STYLES_SRC),html/$(notdir $(style)))

.PHONY: all
all: html/UCC.html $(STYLES_DST) $(FONTS_DST)

html/%.md: %.lagda.md
	$(AGDA) $(AGDA_FLAGS) $<

html/%.html: html/%.md style.css $(FONTS_DST)
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<

html/fonts/%.otf: fonts/%.otf
	@mkdir -p html/fonts
	cp $< $@

html/%.css: %.css
	cp $< $@