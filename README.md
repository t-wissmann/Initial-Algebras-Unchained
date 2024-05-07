# Agda Formalization of 'Initial Algebras Unchained'

<!--
This archive contains both the agda source files and its HTML documentation
with clickable links for easier navigation (see `html/index.html`).
It is not necessary to compile the source again.

If it is still desired to compile the proofs again, the installation of the
following dependencies is required:
-->

You can browse the html documentation of this Agda formalization on

  * https://unchained.nfshost.com/iau-l24/

## Dependencies

  - agda (version 2.6.4)
  - agda-categories (v0.2.0)
  - agda-stdlib (v2.0, implicitly required by agda-categories)

If agda itself is already installed, the following sections describe the
installation of the required libraries and the compilation of the proofs of the
present project.

## Installing the dependencies

```bash
AGDA_DIR=$HOME/.agda/
mkdir -p "$AGDA_DIR"
echo -n > ${AGDA_DIR}/defaults
git clone --depth 1 --branch "v2.0"  "https://github.com/agda/agda-stdlib" "$AGDA_DIR/stdlib-2.0.0"
git clone --depth 1 --branch "v0.2.0"  "https://github.com/agda/agda-categories" "$AGDA_DIR/categories-2.0.0"
find "$AGDA_DIR/stdlib-2.0.0" "$AGDA_DIR/categories-2.0.0" -name '*.agda-lib' | tee ${AGDA_DIR}/libraries
```

## Compiling the project

Checking all the proofs:
```bash
agda src/index.agda
```

Generating the html documentation:
```bash
mkdir -p html
agda --html --html-dir=html/ src/index.agda
```
