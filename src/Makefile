NAME=DobCert
BUILD=.build

CP=cp
UNAME := $(shell uname -s)
ifeq ($(UNAME),Darwin)
	CP=gcp
endif

.PHONY: main clean

main:
	mkdir $(BUILD) 2> /dev/null || true
	find . -path ./$(BUILD) -prune -o -name '*.v' -print | xargs $(CP) -a --parents -t $(BUILD)
	cd $(BUILD); find . -name '*.v' | xargs coq_makefile -R . $(NAME) -o Makefile
	sed -i.bak "s/coq/hoq/" $(BUILD)/Makefile
	make -j4 -C$(BUILD)

clean:
	rm -r $(BUILD)
