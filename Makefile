.PHONY: build test rust lean extract doctor audit install-tools smoke-tools minimal verify-minimal curve verify-curve compare-intermediates vectors verify-vectors pairing
PYTHON ?= python3.11

install-tools:
	bash scripts/install-tools.sh

smoke-tools:
	$(PYTHON) scripts/smoke_tools.py

verify-minimal:
	$(PYTHON) scripts/verify_minimal.py

minimal: test verify-minimal
	$(PYTHON) scripts/offline_cargo.py test --test minimal

verify-curve:
	$(PYTHON) scripts/verify_curve.py

compare-intermediates:
	$(PYTHON) scripts/compare_arkworks_intermediates.py

verify-vectors: lean
	$(PYTHON) scripts/verify_vectors.py

pairing: lean
	$(PYTHON) scripts/offline_cargo.py build --release --bin pairing_example
	cd lean && lake build pairing_example
	$(PYTHON) scripts/eip2537_vectors.py

vectors: rust lean verify-vectors pairing
	$(PYTHON) scripts/offline_cargo.py build --release --bin curve_codec
	$(PYTHON) scripts/published_vectors.py
	$(PYTHON) scripts/offline_cargo.py test --release --config profile.release.overflow-checks=true --test curve rfc9380_published_g1_coordinates

curve: lean verify-curve compare-intermediates vectors
	$(PYTHON) scripts/offline_cargo.py test --release --config profile.release.overflow-checks=true --test curve --test decoder
	$(PYTHON) scripts/offline_cargo.py build --release --bin curve_codec
	$(PYTHON) scripts/curve_differential.py

build: rust lean

rust:
	$(PYTHON) scripts/offline_cargo.py build --release --bin codec

lean:
	cd lean && lake build

test: build audit vectors
	$(PYTHON) scripts/differential.py

audit: lean
	cd lean && lake env lean Audit.lean

doctor:
	$(PYTHON) scripts/extract.py --check

extract:
	$(PYTHON) scripts/extract.py
