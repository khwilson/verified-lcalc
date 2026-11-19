.PHONY: check format test

check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked ty check --error-on-warning

format:
	uv run --locked ruff check --fix .
	uv run --locked ruff format .

test:
	uv run --locked pytest
