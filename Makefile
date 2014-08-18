tersmu: *.hs Pappy
	ghc -o tersmu -iPappy -XMultiParamTypeClasses -XFunctionalDependencies \
	    -XTypeSynonymInstances -XFlexibleInstances --make Main
Pappy:
	mkdir Pappy
	cd Pappy && \
	wget http://pdos.csail.mit.edu/~baford/packrat/thesis/pappy.tgz && \
	tar -xzf pappy.tgz && \
	rm pappy.tgz && \
	patch < ../Pappy.patch
Pappy/pappy: Pappy
	cd Pappy && \
	ghc --make -package haskell98 -hide-package base -o pappy Main.hs
Tersmu.hs: Tersmu.pappy Pappy/pappy
	Pappy/pappy Tersmu.pappy
test: tersmu
	rlwrap ./tersmu
