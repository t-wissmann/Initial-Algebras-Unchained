#!/usr/bin/env bash

mkdir -p _html/

for i in *.agda ; do
    agda --html --html-dir=_html/ "$i"
done


