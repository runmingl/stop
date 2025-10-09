ZIP_NAME = stop.zip

.PHONY: all clean

all:
	find . -type f \( -name '*.agda' -o -name '*.agda-lib' -o -name '*.md' \) | zip $(ZIP_NAME) -@

clean:
	rm -f $(ZIP_NAME)