CURRENT_DIR = .
SETS_DIR = sets
BASIC_DIR = basic
ALGO_DIR = algorithm
COQC = coqc
COQDEP = coqdep
COQ_FLAG = 
DEP_FLAG = -R $(SETS_DIR) SetsClass -R $(BASIC_DIR) Basic -R $(ALGO_DIR) Algorithm

SETS_FLAG = -R $(SETS_DIR) SetsClass
SETS_FILE_NAMES = \
   SetsClass.v SetsDomain.v SetElement.v RelsDomain.v SetElementProperties.v SetProd.v SetsClass_AxiomFree.v SetsDomain_Classic.v
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)

BASIC_FLAG = -R $(BASIC_DIR) Basic -R $(SETS_DIR) SetsClass
BASIC_FILE_NAMES = \
   AlgebraicStructure.v InductiveType.v Logic.v SetsAndRels.v SimpleProofsAndDefs.v 
BASIC_FILES=$(BASIC_FILE_NAMES:%.v=$(BASIC_DIR)/%.v)

ALGO_FLAG = -R $(ALGO_DIR) Algorithm -R $(SETS_DIR) SetsClass
ALGO_FILE_NAMES = \
   Perm.v Sort.v Merge.v
ALGO_FILES=$(ALGO_FILE_NAMES:%.v=$(ALGO_DIR)/%.v)

FILES = $(SETS_FILES) \
  $(BASIC_FILES) \
  $(ALGO_FILES)

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(SETS_FLAG) $<

$(BASIC_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(BASIC_FLAG) $<

$(ALGO_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(ALGO_FLAG) $<

all: \
  $(FILES:%.v=%.vo) \

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob
	@rm -f *.vo */*.vo 
	@rm -f *.vok */*.vok
	@rm -f *.vos */*.vos 
	@rm -f .*.aux */.*.aux 
	@rm -f .depend

.DEFAULT_GOAL := all
-include .depend
