OUTPUT=dist/build/app/app.jsexe/
STATICS=index.html euler.woff typicons.* *.min.js cmunfonts *.holbert
all:
	cabal build && cp -R $(STATICS) $(OUTPUT)
server:
	cd $(OUTPUT) && python3 -m http.server
