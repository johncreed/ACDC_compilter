#! /bin/bash

./AcDc test/sample$1.ac > out.txt
diff out.txt test/sample$1.ac.ans
