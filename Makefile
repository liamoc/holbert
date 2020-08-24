all:
	cabal build && cp index.html dist/build/app/app.jsexe/index.html && cp euler.woff dist/build/app/app.jsexe/euler.woff && cp typicons.* dist/build/app/app.jsexe/ && cp -R computer-modern-web-font-master dist/build/app/app.jsexe/cmunfonts && cp split.min.js dist/build/app/app.jsexe/
