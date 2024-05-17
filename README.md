# Agda Formalization of 'Initial Algebras Unchained'

This is the formalization from the Paper 'Initial Algebras Unchained - A Novel
Initial Algebra Construction Formalized in Agda' accepted for publication at
LICS 2024.

  * A preprint version is available here: https://arxiv.org/abs/2405.09504

You can browse the html documentation of this Agda formalization online:

  * https://arxiv.org/src/2405.09504/anc/index.html
  * https://thorsten-wissmann.de/archive/init-alg-lics24/

## Dependencies

  - agda (version 2.6.4)
  - agda-categories (v0.2.0)
  - agda-stdlib (v2.0, implicitly required by agda-categories)

Assuming that Agda is already installed, the following sections describe the
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
