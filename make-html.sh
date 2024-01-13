#!/usr/bin/env bash

mkdir -p _html/

agda --html --html-dir=_html/ "index.agda"

echo "open the doc in your browser: file://`pwd`/_html/index.html"

if [[ "$1" = --install ]] ; then
    rsync -rva _html/ uber:html/initial-algebras-unchained
    cat <<EOF

    ====>   https://thorsten-wissmann.de/initial-algebras-unchained/
EOF
fi
