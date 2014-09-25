TERSMU=../tersmu
all: 1.loj 2.loj 3.loj 4.loj 5.loj 6.loj 7.loj 8.loj 9.loj 10.loj 11.loj\
	12.loj 13.loj 14.loj 15.loj 16.loj 17.loj 18.loj 19.loj
%.loj: %.jbo ${TERSMU} 
	./tersmuLines < $< > $@

alis.loj: alis
	sed 's/^$$/%%%PARABREAK%%%/g' < $< | tr -d '\n' | sed 's/  */ /g' | sed 's/%%%PARABREAK%%%/\n/g' | tersmuLines > $@
