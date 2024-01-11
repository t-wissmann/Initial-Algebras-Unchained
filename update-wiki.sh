#!/usr/bin/env bash

HTML=_html/
WIKI="$1"

debug() {
    echo -e "\e[1;33m:: \e[0;32m$*\e[0m" >&2
}

if [ -z "$WIKI" ] ; then
    debug "Pass WIKI directory as \$1"
    exit 1
fi

css="$HTML/Agda.css"

for i in "$HTML"/*.html ; do
    target="$WIKI/${i##*/}.md"
    debug "Writing $target"
    sed -f inline-agda-style.sed "${i}" > "$target"
done

sidebarmd="$WIKI/_sidebar.md"
debug "Writing $sidebarmd"
for i in $(find -name '*.agda' |sort|uniq) ; do
    depth=$(sed 's,[^/],,g;s,/,  ,g' <<< "$i")
    i=${i#./} # strip leading ./
    filename=${i#*/}
    basename=${filename%.*} # strip file extension
    module="${i%.*}"
    module="${module//\//.}"
    echo "$depth* [$module]($module.html)"
done > "$sidebarmd"

