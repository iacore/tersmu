Tersmu.hs: Tersmu.pappy
	Pappy/pappy Tersmu.pappy
test: Tersmu.hs
	rlwrap runhugs -P:Pappy Main.hs
FOLtest: FOL.hs
	runhugs FOL.hs
