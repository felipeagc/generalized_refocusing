.DEFAULT_GOAL := all


.DEFAULT:
	cd Lib                 && $(MAKE) $@
	cd rewriting_system    && $(MAKE) $@
	cd abstract_machine    && $(MAKE) $@
	cd reduction_semantics && $(MAKE) $@
	cd refocusing          && $(MAKE) $@
	cd examples && $(MAKE) $@