package main

import (
	"context"
	"cs.utexas.edu/zjia/faas"
	"cs.utexas.edu/zjia/faas/types"
	"fmt"
	"github.com/eniac/ccmesh/pkg/base"
)

type Handler struct {
	env types.Environment
}

type funcHandlerFactory struct {
}

func (f *funcHandlerFactory) New(env types.Environment, funcName string) (types.FuncHandler, error) {
	if funcName == "Entry" {
		return &Handler{env: env}, nil
	} else {
		return nil, nil
	}
}

func (f *funcHandlerFactory) GrpcNew(env types.Environment, service string) (types.GrpcFuncHandler, error) {
	return nil, fmt.Errorf("Not implemented")
}

func (h *Handler) Call(ctx context.Context, input []byte) ([]byte, error) {
	res := base.Run(input)
	return res, nil
}

func main() {
	faas.Serve(&funcHandlerFactory{})
}
