OUTPUT=dist-newstyle/build/x86_64-linux/ghcjs-8.6.0.1/holbert-0.1.0.0/x/app/build/app/app.jsexe/
STATICS=index.html euler.woff typicons.* split.min.js cmunfonts
all:
	cabal build && cp -R $(STATICS) $(OUTPUT)
open:
	open $(OUTPUT)/index.html
