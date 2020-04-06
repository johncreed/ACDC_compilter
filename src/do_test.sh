#! /bin/bash

./AcDc test/sample$1.ac out.txt

cat out.txt
echo "===================================="
cat test/sample$1.ac
