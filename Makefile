TSLSAT=tslsat
TSLFUZZ=tslfuzz
TSL2BSA=tsl2bsa

TOOLS=\
  ${TSLSAT}\
  ${TSLFUZZ}\
  ${TSL2BSA}

STACKPATH=$(shell if [ -d "dist" ]; then echo ""; else stack path | grep local-install-root | sed 's/local-install-root: //'; fi)
BLDTOOL=$(shell if [ -d "dist" ]; then echo "cabal"; else echo "stack"; fi)

default:
	${BLDTOOL} build
	@for i in ${TOOLS}; do if [ -d "dist" ]; then cp ./dist/build/$${i}/$${i} $${i}; else cp ${STACKPATH}/bin/$${i} $${i}; fi; done

${TSLSAT}:
	${BLDTOOL} build :$@
	@if [ -d "dist" ]; then cp ./dist/build/$@/$@ $@; else cp ${STACKPATH}/bin/$@ $@; fi

${TSLFUZZ}:
	${BLDTOOL} build :$@
	@if [ -d "dist" ]; then cp ./dist/build/$@/$@ $@; else cp ${STACKPATH}/bin/$@ $@; fi

${TSL2BSA}:
	${BLDTOOL} build :$@
	@if [ -d "dist" ]; then cp ./dist/build/$@/$@ $@; else cp ${STACKPATH}/bin/$@ $@; fi

install:
	${BLDTOOL} install

clean:
	${BLDTOOL} clean
	@for i in ${TOOLS}; do rm -f $${i}; done

.PHONY: install clean ${TOOLS}
.SILENT:
