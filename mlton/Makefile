## Copyright (C) 2010,2013,2016,2018-2020 Matthew Fluet.
 # Copyright (C) 1999-2009 Henry Cejtin, Matthew Fluet, Suresh
 #    Jagannathan, and Stephen Weeks.
 # Copyright (C) 1997-2000 NEC Research Institute.
 #
 # MLton is released under a HPND-style license.
 # See the file MLton-LICENSE for details.
 ##

ROOT := ..
include $(ROOT)/Makefile.config

######################################################################

RUN_MLTON_RUNTIME_XARGS := ram-slop 0.7
RUN_MLTON_COMPILE_XARGS :=

ifeq (true, $(SELF_COMPILE))
# Older versions of `mlton` may not support `sequenceNonUnit` or `warnUnused`.
RUN_MLTON_COMPILE_XARGS += -default-ann 'sequenceNonUnit warn'
RUN_MLTON_COMPILE_XARGS += -default-ann 'warnUnused true'
# RUN_MLTON_COMPILE_XARGS += -type-check true
# We're self-compiling, so don't use any stubs.
MLTON_MLB := mlton.mlb
else
ifneq (, $(findstring $(HOST_OS),cygwin mingw))
# We're bootstrapping on Cygwin or MinGW; stubs define `spawn` in terms of
# `fork` and `fork` doesn't work on Cygwin or MinGW, so don't use any stubs.
MLTON_MLB := mlton.mlb
else
# We're bootstrapping, so use stubs.
MLTON_MLB := mlton-stubs.mlb
endif
endif

## When self-compiling the current MLton sources with `Zone` enabled,
## the resulting compiler exhibits a space leak; see MLton/mlton#334
ifeq ($(RUN_MLTON_VERSION), $(firstword $(sort $(RUN_MLTON_VERSION) 20170629)))
RUN_MLTON_COMPILE_XARGS += -drop-pass zone
else ifeq ($(RUN_MLTON_VERSION), $(firstword $(sort $(RUN_MLTON_VERSION) 20191003)))
RUN_MLTON_COMPILE_XARGS += -disable-pass zone
endif

FRONT_END_SOURCES :=		\
	front-end/ml.lex.sml	\
	front-end/ml.grm.sig	\
	front-end/ml.grm.sml	\
	front-end/mlb.lex.sml	\
	front-end/mlb.grm.sig	\
	front-end/mlb.grm.sml

SOURCES :=			\
	$(MLTON_MLB)		\
	$(FRONT_END_SOURCES)	\
	control/version.sml	\
	$(shell if [ -e $(MLTON_MLB) ]; then "$(RUN_MLTON_DEPS)" -stop f $(MLTON_MLB); fi)

.PHONY: all
all: $(MLTON_OUTPUT)

.PHONY: clean
clean:
	$(SRC)/bin/clean

SHOW_VARS += MLTON_MLB
$(eval $(MK_SHOW_CONFIG))

######################################################################

$(MLTON_OUTPUT): $(SOURCES)
	@echo 'Compiling mlton'
	"$(RUN_MLTON)" \
		@MLton $(RUN_MLTON_RUNTIME_XARGS) $(RUN_MLTON_RUNTIME_ARGS) gc-summary -- \
		$(RUN_MLTON_COMPILE_XARGS) -verbose 2 $(RUN_MLTON_COMPILE_ARGS)	\
		-target $(TARGET) -output $(MLTON_OUTPUT)			\
		$(MLTON_MLB)

ifeq ($(shell (cat control/version_sml.src; echo $(MLTON_NAME) $(MLTON_VERSION); if [ -e control/version.sml ]; then cat control/version.sml; fi) | $(SHA1DGST)),$(shell if [ -e control/version_sml.chk ]; then cat control/version_sml.chk; fi))
control/version.sml: control/version_sml.src
	touch control/version.sml
else
$(shell $(RM) control/version.sml)
control/version.sml: control/version_sml.src
	$(SED) \
		-e "s/MLTON_NAME/$(MLTON_NAME)/" \
		-e "s/MLTON_VERSION/$(MLTON_VERSION)/" \
		< control/version_sml.src \
		> control/version.sml
	(cat control/version_sml.src; echo $(MLTON_NAME) $(MLTON_VERSION); cat control/version.sml) | $(SHA1DGST) > control/version_sml.chk
endif

front-end/%.lex.sml: front-end/%.lex
	$(RM) $<.*
	$(RUN_MLLEX) $<
	$(MV) $<.sml $<.sml.in
	$(SED) -e 's/val s = List.map f (List.rev (tl (List.rev s)))/val s = Pervasive.List.map f (Pervasive.List.rev (tl (Pervasive.List.rev s)))/' $<.sml.in > $<.sml
	$(MV) $<.sml $<.sml.in
	$(SED) -e 's/in Vector.fromList(List.map g/in Vector.fromList(Pervasive.List.map g/' $<.sml.in > $<.sml
	$(RM) $<.sml.in
	$(CHMOD) -w $<.*

front-end/%.grm.sig front-end/%.grm.sml: front-end/%.grm
	$(RM) $<.*
	$(RUN_MLYACC) $<
	$(MV) $<.sml $<.sml.in
	$(SED) -e 's/in f 0 handle General.Subscript => ()/in f 0 handle Pervasive.General.Subscript => ()/' $<.sml.in > $<.sml
	$(MV) $<.sml $<.sml.in
	$(SED) -e 's/in Array.fromList(List.map actionRowLookUp actionRowNumbers)/in Array.fromList(Pervasive.List.map actionRowLookUp actionRowNumbers)/' $<.sml.in > $<.sml
	$(RM) $<.sml.in
	$(CHMOD) -w $<.*

mlton-stubs.mlb: $(shell "$(RUN_MLTON_DEPS)" -stop f ../lib/stubs/mlton-stubs/sources.mlb | $(GREP) 'mlb$$') $(shell "$(RUN_MLTON_DEPS)" -stop f mlton.mlb | $(GREP) 'mlb$$')
	(									\
		echo '$$(SML_LIB)/basis/unsafe.mlb';				\
		echo '$$(SML_LIB)/basis/sml-nj.mlb';				\
		echo '$$(SML_LIB)/basis/mlton.mlb';				\
		echo '$$(SML_LIB)/basis/basis.mlb';				\
		$(RUN_MLTON) -stop f mlton.mlb |				\
			$(GREP) -v 'mlb$$' |					\
			$(GREP) 'mlyacc';					\
		$(RUN_MLTON) -stop f ../lib/stubs/mlton-stubs/sources.mlb |	\
			$(GREP) -v 'mlb$$' |					\
			$(GREP) 'mlton-stubs';					\
		$(RUN_MLTON) -stop f mlton.mlb |				\
			$(GREP) -v 'mlb$$' |					\
			$(GREP) -v 'sml/basis' |				\
			$(GREP) -v 'targets' |					\
			$(GREP) -v 'mlyacc';					\
	) > mlton-stubs.mlb

######################################################################

.PHONY: def-use
def-use: mlton.def-use

mlton.def-use: $(SOURCES)
	"$(RUN_MLTON)" \
		@MLton $(RUN_MLTON_RUNTIME_XARGS) $(RUN_MLTON_RUNTIME_ARGS) --	\
		$(RUN_MLTON_COMPILE_XARGS) -verbose 0 $(RUN_MLTON_COMPILE_ARGS)	\
		-stop tc -prefer-abs-paths true -show-def-use mlton.def-use	\
		$(MLTON_MLB)

######################################################################

ifneq (,$(REMOTE_TARGET))
mlton-bootstrap-$(REMOTE_TARGET).tgz: $(SOURCES)
	"$(RUN_MLTON)" \
		@MLton $(RUN_MLTON_RUNTIME_XARGS) $(RUN_MLTON_RUNTIME_ARGS) gc-summary -- \
		$(RUN_MLTON_COMPILE_XARGS) -verbose 2 $(RUN_MLTON_COMPILE_ARGS)	\
		-target $(REMOTE_TARGET) -output $(MLTON_OUTPUT) \
		-codegen c -stop g \
		$(MLTON_MLB)
	$(TAR) czf $@ $(MLTON_OUTPUT).*.c
	$(RM) $(MLTON_OUTPUT).*.c
endif

######################################################################

#
# The following rebuilds the heap file for the SML/NJ compiled version of MLton.
#
SMLNJ := sml
SMLNJ_CM_SERVERS_NUM := 0

.PHONY: smlnj-mlton
smlnj-mlton: mlton-smlnj.cm control/version.sml $(FRONT_END_SOURCES)
	(									\
		echo 'SMLofNJ.Internals.GC.messages false;';			\
		echo '#set CM.Control.verbose false;';				\
		echo '#set CM.Control.warn_obsolete true;';			\
		echo 'Control.polyEqWarn := false;';				\
		echo 'local';							\
		echo 'fun loop 0 = () | loop n = (CM.Server.start {cmd = (CommandLine.name (), ["@CMslave"]), name = "server" ^ (Int.toString n), pathtrans = NONE, pref = 0}; loop (n - 1));'; \
		echo 'in';							\
		echo 'val _ = loop $(SMLNJ_CM_SERVERS_NUM);';			\
		echo 'end;';							\
		echo 'if (CM.make "mlton-smlnj.cm") handle _ => false';		\
		echo '   then ()';						\
		echo '   else OS.Process.exit OS.Process.failure;'; 		\
		echo 'SMLofNJ.exportFn("$(MLTON_OUTPUT)-smlnj",Main.main);'	\
	) | "$(SMLNJ)"

######################################################################

#
# The following rebuilds the executable file for the Poly/ML compiled version of
# MLton.
#
POLYML := poly

.PHONY: polyml-mlton
polyml-mlton: mlton-polyml.use $(shell [ -e mlton-polyml.use ] && cat mlton-polyml.use | $(SED) 's/use "\(.*\)";/\1/') control/version.sml $(FRONT_END_SOURCES)
	(									\
		echo 'use "mlton-polyml.use";';					\
		echo 'PolyML.export("$(MLTON_OUTPUT)-polyml", Main.mainWrapped);'; \
	) | "$(POLYML)"
	$(CC) -o $(MLTON_OUTPUT)-polyml $(MLTON_OUTPUT)-polyml.o -lpolymain -lpolyml
	$(RM) $(MLTON_OUTPUT)-polyml.o

mlton-polyml.use: ../lib/stubs/basis-stubs-for-polyml/sources.use ../lib/stubs/mlton-stubs-for-polyml/sources.use $(shell "$(RUN_MLTON_DEPS)" -stop f ../lib/stubs/mlton-stubs/sources.mlb | $(GREP) 'mlb$$') $(shell "$(RUN_MLTON_DEPS)" -stop f mlton.mlb | $(GREP) 'mlb$$')
	(									\
		cat ../lib/stubs/basis-stubs-for-polyml/sources.use |		\
			$(SED) 's|use "\(.*\)";|../lib/stubs/basis-stubs-for-polyml/\1|'; \
		"$(RUN_MLTON)" -stop f mlton.mlb | $(GREP) -v 'mlb$$' | $(GREP) 'mlyacc'; \
		cat ../lib/stubs/mlton-stubs-for-polyml/sources.use |		\
			$(SED) 's|use "\(.*\)";|../lib/stubs/mlton-stubs-for-polyml/\1|'; \
		"$(RUN_MLTON)" -stop f ../lib/stubs/mlton-stubs/sources.mlb |	\
			$(GREP) -v 'mlb$$' |					\
			$(GREP) 'mlton-stubs';					\
		"$(RUN_MLTON)" -stop f mlton.mlb |				\
			$(GREP) -v 'mlb$$' |					\
			$(GREP) -v 'sml/basis' |				\
			$(GREP) -v 'targets' |					\
			$(GREP) -v 'mlton-stubs' |				\
			$(GREP) -v 'mlyacc' |					\
			$(GREP) -v 'call-main.sml';				\
	) | $(SED) 's|\(.*\)|use "\1";|' > mlton-polyml.use
