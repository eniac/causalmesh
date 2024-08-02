#!/bin/bash -ex

rm -f main
/usr/local/go/bin/go build -o main internal/media/main.go
bash ./run_stack_media.sh
