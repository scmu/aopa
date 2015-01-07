AGDA_STD_LIB = /usr/share/agda-stdlib/

check: agda
	agda -i ${AGDA_STD_LIB} -i . Examples/Optimisation/ActivitySelection.agda
	agda -i ${AGDA_STD_LIB} -i . Examples/Sorting/qSort.agda


agda:
	@echo Get Agda from http://code.haskell.org/Agda
