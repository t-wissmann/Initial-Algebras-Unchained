#!/usr/bin/env bash

mkdir -p _html/

agda --html --html-dir=_html/ "index.agda"

echo "open the doc in your browser: file://`pwd`/_html/index.html"

#    rsync -rva _html/ uber:html/initial-algebras-unchained
#    ====>   https://thorsten-wissmann.de/initial-algebras-unchained/

if [[ "$1" = --install ]] ; then
    rsync -rva _html/ thorsten_unchained@ssh.nyc1.nearlyfreespeech.net:/home/public/iau-l24/
    cat <<EOF
    ====>   https://unchained.nfshost.com/iau-l24/
EOF
fi
