all:
	cd parser && $(MAKE)
	cd src && $(MAKE)
	cd lib && $(MAKE)

clean:
	cd parser && $(MAKE) clean
	cd src && $(MAKE) clean
	cd lib && $(MAKE) clean
	rm -rf latc_x86
