all: check-sound check-complete check-fw-sound check-fw-complete

check-sound:
	cbmc main.c --function check_sound --trace

check-complete:
	cbmc main.c --function check_complete --trace

check-fw-sound:
	cbmc main.c --function check_fw_sound --trace

check-fw-complete:
	cbmc main.c --function check_fw_complete --trace

.PHONY: all check-sound check-complete check-fw-sound check-fw-complete
