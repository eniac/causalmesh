package lib

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
)

func UploadMovieReview(client *GoClient, movieId string, reviewId string) string {
	reviewsResp := client.Read(fmt.Sprintf("movieReview.%s", movieId))
	var reviews []string
	err := json.Unmarshal([]byte(reviewsResp), &reviews)
	CHECK(err)
	reviews = append(reviews, reviewId)
	if len(reviews) > 10 {
		reviews = reviews[1:]
	}
	reviewsStr, err := json.Marshal(reviews)
	CHECK(err)
	client.Write(fmt.Sprintf("movieReview.%s", movieId), string(reviewsStr))
	return ""
}

func ReadMovieReviews(client *GoClient, movieId string) string {
	var reviewIds []string
	res := client.Read(fmt.Sprintf("movieReview.%s", movieId))
	//fmt.Println(movieId, res)
	err := json.Unmarshal([]byte(res), &reviewIds)
	CHECK(err)
	reviewIdsStr, err := json.Marshal(reviewIds)
	CHECK(err)
	return string(reviewIdsStr)
}
