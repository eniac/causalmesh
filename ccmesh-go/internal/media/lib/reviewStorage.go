package lib

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
)

func StoreReview(client *GoClient, review Review) string {
	reviewStr, err := json.Marshal(review)
	CHECK(err)
	client.Write(fmt.Sprintf("reviewStorage.%s", review.ReviewId), string(reviewStr))
	return ""
}

func ReadReviews(client *GoClient, ids []string) string {
	var reviews []Review
	for _, id := range ids {
		var review Review
		res := client.Read(fmt.Sprintf("reviewStorage.%s", id))
		err := json.Unmarshal([]byte(res), &review)
		CHECK(err)
		reviews = append(reviews, review)
	}
	reviewsStr, err := json.Marshal(reviews)
	CHECK(err)
	return string(reviewsStr)
}
