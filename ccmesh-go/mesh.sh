#!/bin/bash -ex

rm -f main
/usr/local/go/bin/go build -o main internal/ccmesh/main.go
bash ./run_stack.sh
