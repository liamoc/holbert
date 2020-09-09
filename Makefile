OUTPUT=dist-newstyle/build/x86_64-linux/ghcjs-8.6.0.1/holbert-0.2.0.0/x/app/build/app/app.jsexe/
STATICS=index.html euler.woff typicons.* *.min.js cmunfonts *.holbert
all:
	cabal build && cp -R $(STATICS) $(OUTPUT)
server:
	cd $(OUTPUT) && python3 -m http.server
