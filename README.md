# Agda Formalization of 'Initial Algebras Unchained'

Dependencies:

  - agda-categories (v0.1.7.2)
  - agda-stdlib (v1.7.2, implicitly required by agda-categories)

## Installing the dependencies

```bash
AGDA_DIR=$HOME/.agda/
mkdir -p "$AGDA_DIR"
echo -n > ${AGDA_DIR}/defaults
git clone --depth 1 --branch "v1.7.2"  "https://github.com/agda/agda-stdlib" "$AGDA_DIR/stdlib-1.7.2"
git clone --depth 1 --branch "v0.1.7.2"  "https://github.com/agda/agda-categories" "$AGDA_DIR/categories-1.7.2"
find "$AGDA_DIR/stdlib-1.7.2" "$AGDA_DIR/categories-1.7.2" -name '*.agda-lib' | tee ${AGDA_DIR}/libraries
```

## Compiling the project

Checking all the proofs:
```bash
agda index.agda
```

Generating the html documentation:
```bash
mkdir -p html
agda --html --html-dir=html/ index.agda
```
