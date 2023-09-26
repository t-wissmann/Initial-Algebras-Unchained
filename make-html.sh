#!/usr/bin/env bash

mkdir -p _html/

agda --html --html-dir=_html/ "index.agda"

echo "open the doc in your browser: file://`pwd`/_html/index.html"

