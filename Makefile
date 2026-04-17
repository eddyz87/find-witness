all: check-sound check-complete

check-sound:
	cbmc main.c --function check_sound --trace

check-complete:
	cbmc main.c --function check_complete --trace

.PHONY: all check-sound check-complete
