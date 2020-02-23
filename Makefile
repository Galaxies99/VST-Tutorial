CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

COQ_FLAG = -Q . EV \
	   -Q $(VSTDIR)/msl VST.msl \
	   -Q $(VSTDIR)/sepcomp VST.sepcomp \
	   -Q $(VSTDIR)/veric VST.veric \
	   -Q $(VSTDIR)/floyd VST.floyd \
	   -Q $(VSTDIR)/progs VST.progs \
	   -R $(VSTDIR)/compcert compcert

DEP_FLAG = -Q . EV \
	   -Q $(VSTDIR)/msl VST.msl \
	   -Q $(VSTDIR)/sepcomp VST.sepcomp \
	   -Q $(VSTDIR)/veric VST.veric \
	   -Q $(VSTDIR)/floyd VST.floyd \
	   -Q $(VSTDIR)/progs VST.progs \
	   -R $(VSTDIR)/compcert compcert

FILES = \
  reverse.v add.v append.v max3.v swap.v tri.v abs.v gcd.v fact.v test_null.v AuxiliaryTac.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo) \

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*/*.vo */*/*.glob

.DEFAULT_GOAL := all

include .depend

