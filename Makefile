all:
	cd parser && $(MAKE)
	cd src && $(MAKE)

clean:
	cd parser && $(MAKE) clean
	cd src && $(MAKE) clean
	rm -rf insc_jvm insc_llvm
	rm -rf doc/Instant/*.bc
	rm -rf doc/Instant/*.ll
	rm -rf doc/Instant/*.j
	rm -rf doc/Instant/*.class
	rm -rf *out
