NAME=Cosette
BUILD=.build

CP=cp
UNAME := $(shell uname -s)
ifeq ($(UNAME),Darwin)
	CP=gcp
endif

.PHONY: main clean post

main:
	mkdir $(BUILD) 2> /dev/null || true
	find . -path ./$(BUILD) -prune -o -name '*.v' -print | xargs $(CP) -a --parents -t $(BUILD)
	cd $(BUILD); find . -name '*.v' | xargs coq_makefile -R . $(NAME) -o Makefile
	sed -i.bak "s/coq/hoq/" $(BUILD)/Makefile
	make -j4 -C$(BUILD)

post:
	coqdoc --html --body-only --no-index --parse-comments BlogPost.v
	sed -i.bak 's|<div class="paragraph"> </div>|<p/>|g' BlogPost.html
	sed -i.bak 's|class="code"|style="font-family: monospace; padding-left: 2em"|g' BlogPost.html
	sed -i.bak 's|class="inlinecode"|style="font-family: monospace"|g' BlogPost.html
	sed -i.bak 's|class="id" title="var"|style="color: #660066"|g' BlogPost.html
	sed -i.bak 's|class="id" title="keyword"|style="color: #cf1d1d"|g' BlogPost.html
	sed -i.bak 's|class="id" title="tactic"|style="color: #000000"|g' BlogPost.html
	sed -i.bak 's|class="comment"|style="color: #8080cc"|g' BlogPost.html
	sed -i.bak 's|<h1.*/h1>||g' BlogPost.html
	sed -i.bak 's| class="doc"||g' BlogPost.html
	rm coqdoc.css 

clean:
	rm -rf $(BUILD)
	rm -f BlogPost.html
