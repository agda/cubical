#!/bin/bash

agdaipath=`agda --version | sed -n 's/.* \([0-9]\+\.[0-9]\+\.[0-9]\+\).*/\1/p'`

all-imported-files() {
    filename="$1"
    grep -v '^--' $filename | grep -o -e "import[[:space:]]Cubical[][A-Za-z0-9.-]*" | sed -E 's/\./\//g; s/^import (.*)$/\1.agda/; s/ //g'
}

agdai-name() {
    filename="$1"
    echo "_build/$agdaipath/agda/$(echo $filename)i"
}

echo '.PHONY : check'
for filename in `find -type f -name '*.agda' | sed 's/^[\/.]\+//'`; do
    echo "check: $(agdai-name $filename)"
done

echo ""
echo ""

for filename in `find -type f -name '*.agda' | sed 's/^[\/.]\+//'`; do
    echo "$(agdai-name $filename): $filename"
    for imported_file in `all-imported-files $filename`; do
	echo "$(agdai-name $filename):  $(agdai-name $imported_file)"
    done

    echo "	\$(AGDA) $filename"
    echo ""
done
