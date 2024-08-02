#!/bin/bash -ex

rm -f main
/usr/local/go/bin/go build -o main internal/hzopt/main.go
bash ./run_stack.sh
