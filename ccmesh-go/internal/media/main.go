package main

import (
	"context"
	"cs.utexas.edu/zjia/faas"
	"cs.utexas.edu/zjia/faas/types"
	"encoding/json"
	"fmt"
	"github.com/eniac/ccmesh/internal/media/lib"
	. "github.com/eniac/ccmesh/pkg/common"
)

type ComposeHandler struct {
	env types.Environment
}

type MovieReviewHandler struct {
	env types.Environment
}

type UserReviewHandler struct {
	env types.Environment
}

type ReviewStorageHandler struct {
	env types.Environment
}

type InitHandler struct {
	env types.Environment
}

type funcHandlerFactory struct {
}

func (f *funcHandlerFactory) New(env types.Environment, funcName string) (types.FuncHandler, error) {
	if funcName == "composeReview" {
		return &ComposeHandler{env: env}, nil
	} else if funcName == "movieReview" {
		return &MovieReviewHandler{env: env}, nil
	} else if funcName == "userReview" {
		return &UserReviewHandler{env: env}, nil
	} else if funcName == "reviewStorage" {
		return &ReviewStorageHandler{env: env}, nil
	} else if funcName == "init" {
		return &InitHandler{env: env}, nil
	} else {
		return nil, nil
	}
}

func (f *funcHandlerFactory) GrpcNew(env types.Environment, service string) (types.GrpcFuncHandler, error) {
	return nil, fmt.Errorf("Not implemented")
}

func (h *ComposeHandler) Call(ctx context.Context, input []byte) ([]byte, error) {
	client := lib.NewGoClient(input)
	var req AnyJson
	err := json.Unmarshal([]byte(client.GetInput()), &req)
	CHECK(err)
	res := ""
	switch req["Function"] {
	//case "UploadUniqueId":
	//	lib.UploadUniqueId(client, req["reqId"].(string), req["reviewId"].(string))
	case "UploadText":
		res = lib.UploadText(client, req["req_id"].(string), req["text"].(string))
	case "UploadRating":
		res = lib.UploadRating(client, req["req_id"].(string), req["rating"].(string))
	case "UploadUserId":
		res = lib.UploadUserId(client, req["req_id"].(string), req["user_id"].(string))
	case "UploadMovieId":
		res = lib.UploadMovieId(client, req["req_id"].(string), req["movie_id"].(string))
	case "ComposeAndUpload":
		res = lib.ComposeAndUpload(client, req["req_id"].(string))
	}
	client.SetInput(res)
	client.Finish()
	clientStr := lib.SeGoClient(client)
	return clientStr, nil
}

func (h *MovieReviewHandler) Call(ctx context.Context, input []byte) ([]byte, error) {
	client := lib.NewGoClient(input)
	var req AnyJson
	err := json.Unmarshal([]byte(client.GetInput()), &req)
	CHECK(err)
	res := ""
	switch req["Function"] {
	case "UploadMovieReview":
		res = lib.UploadMovieReview(client, req["movie_id"].(string), req["review_id"].(string))
	case "ReadMovieReviews":
		res = lib.ReadMovieReviews(client, req["movie_id"].(string))
	}
	client.SetInput(res)
	client.Finish()
	clientStr := lib.SeGoClient(client)
	return clientStr, nil
}

func (h *UserReviewHandler) Call(ctx context.Context, input []byte) ([]byte, error) {
	client := lib.NewGoClient(input)
	var req AnyJson
	err := json.Unmarshal([]byte(client.GetInput()), &req)
	CHECK(err)
	switch req["Function"] {
	case "UploadUserReview":
		lib.UploadUserReview(client, req["user_id"].(string), req["review_id"].(string))
	}
	client.Finish()
	clientStr := lib.SeGoClient(client)
	return clientStr, nil
}

func (h *ReviewStorageHandler) Call(ctx context.Context, input []byte) ([]byte, error) {
	client := lib.NewGoClient(input)
	var req AnyJson
	err := json.Unmarshal([]byte(client.GetInput()), &req)
	CHECK(err)
	res := ""
	switch req["Function"] {
	case "StoreReview":
		var review lib.Review
		err := json.Unmarshal([]byte(req["review"].(string)), &review)
		CHECK(err)
		res = lib.StoreReview(client, review)
	case "ReadReviews":
		var ids []string
		err := json.Unmarshal([]byte(req["ids"].(string)), &ids)
		CHECK(err)
		res = lib.ReadReviews(client, ids)
	}
	client.SetInput(res)
	client.Finish()
	clientStr := lib.SeGoClient(client)
	return clientStr, nil
}

func (h *InitHandler) Call(ctx context.Context, input []byte) ([]byte, error) {
	//client := lib.NewGoClient(input)
	return []byte("ok"), nil
}

func main() {
	faas.Serve(&funcHandlerFactory{})
}
