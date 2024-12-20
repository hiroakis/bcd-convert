.PHONY: test
test:
	cargo test -- --nocapture

.PHONY: doc
doc:
	cargo doc

.PHONY: open-doc
open-doc:
	cargo doc --open
