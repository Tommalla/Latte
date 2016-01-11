all: latc_x86

latc_x86: Main.hs Common.hs Compiler.hs Translator.hs TypeChecker.hs
	ghc Main.hs -i../parser -o ../latc_x86

clean:
	rm -rf *.o *.hi
