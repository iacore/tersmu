Tersmu.hs: Tersmu.pappy
	cd .. && ./pappy tersmu/Tersmu.pappy
test: Tersmu.hs
	cd .. && runhugs tersmu/Main.hs
FOLtest: FOL.hs
	cd .. && runhugs tersmu/FOL.hs
