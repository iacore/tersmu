Tersmu.hs: Tersmu.pappy
	Pappy/pappy Tersmu.pappy
Main: *.hs
	ghc -iPappy -XMultiParamTypeClasses -XFunctionalDependencies -XTypeSynonymInstances -XFlexibleInstances --make Main
#test: Tersmu.hs
	#rlwrap runhugs -P:Pappy Main.hs
test: Main
	rlwrap ./Main
FOLtest: FOL.hs
	runhugs FOL.hs
