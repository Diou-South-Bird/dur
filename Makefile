# Original at [https://gist.github.com/sighingnow/deee806603ec9274fd47]
# Thank thee ^_^
all: cargo
.PHONY: all

os :=
ifeq ($(OS),Windows_NT)
	os += cargo rustc -- -C link-args="/ENTRY:_start /SUBSYSTEM:console" -C no-redzone=true
else
	uname_s := $(shell uname -s)
	ifeq ($(uname_s),Linux)
		os += cargo rustc -- -C link-arg=-nostartfiles -C no-redzone=true
	endif
	ifeq ($(uname_s),Darwin)
		os += cargo rustc -- -C link-args="-e __start -static -nostartfiles" -C no-redzone=true
	endif
endif

cargo:
	$(os)

$(V).SILENT:
