#! /bin/bash

./AcDc $1 > out.txt
diff out.txt $1.ans
