CBMC_BIN = /home/ezingerman/cbmc/build/bin
GOTO_CC = $(CBMC_BIN)/goto-cc
GOTO_INSTRUMENT = $(CBMC_BIN)/goto-instrument
CBMC = $(CBMC_BIN)/cbmc

all: check-sound check-complete check-fw-sound check-fw-complete

check-sound:
	cbmc main.c --function check_sound --trace

check-complete:
	cbmc main.c --function check_complete --trace

main.gb: main.c
	$(GOTO_CC) main.c -o main.gb

enforced.gb: main.gb
	$(GOTO_INSTRUMENT) --enforce-contract find_witness_aux main.gb enforced.gb

replaced.gb: main.gb
	$(GOTO_INSTRUMENT) --replace-call-with-contract find_witness_aux main.gb replaced.gb

check-contract: enforced.gb
	$(CBMC) enforced.gb --function check_sound --smt2

check-fw-sound: replaced.gb
	$(CBMC) replaced.gb --function check_fw_sound --smt2 --trace

check-fw-complete: replaced.gb
	$(CBMC) replaced.gb --function check_fw_complete --smt2 --trace

clean:
	rm -f main.gb enforced.gb replaced.gb

.PHONY: all check-sound check-complete check-contract check-fw-sound check-fw-complete clean
