OUTPUT=dist/build/app/app.jsexe/
OUTPUT_NEWSTYLE=dist-newstyle/build/x86_64-linux/ghcjs-8.6.0.1/holbert-0.5.1.0/x/app/build/app/app.jsexe/
STATICS=index.html favicon.PNG euler.woff typicons.* *.min.js cmunfonts *.holbert
all:
	cabal build && cp -R $(STATICS) $(OUTPUT)
newstyle:
	cabal build && cp -R $(STATICS) $(OUTPUT_NEWSTYLE)
server:
	cd $(OUTPUT) && python3 -m http.server
server_newstyle:
	cd $(OUTPUT_NEWSTYLE) && python3 -m http.server
