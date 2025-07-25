#!/bin/bash

for filename in `cat agda-files`; do
    echo $filename `agda --profile=modules $filename | head -n 1 | sed 's/^Total //'`
done					  
