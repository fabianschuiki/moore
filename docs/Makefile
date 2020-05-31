all: queries.png

.PHONY: all

queries.png: queries.dot
	dot $< -Tpng -o $@
