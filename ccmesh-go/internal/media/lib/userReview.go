package lib

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
)

func UploadUserReview(client *GoClient, userId string, reviewId string) {
	reviewsResp := client.Read(fmt.Sprintf("userReview.%s", userId))
	var reviews []string
	err := json.Unmarshal([]byte(reviewsResp), &reviews)
	CHECK(err)
	reviews = append(reviews, reviewId)
	if len(reviews) > 10 {
		reviews = reviews[1:]
	}
	reviewsStr, err := json.Marshal(reviews)
	CHECK(err)
	client.Write(fmt.Sprintf("userReview.%s", userId), string(reviewsStr))
}
