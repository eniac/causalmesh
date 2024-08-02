package lib

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
	"io/ioutil"
)

func Init(client *GoClient) {
	data, err := ioutil.ReadFile("/home/WS/ccmesh-go/internal/media/compressed.json")
	CHECK(err)
	var movies []MovieInfo
	err = json.Unmarshal(data, &movies)
	CHECK(err)
	empty, err := json.Marshal([]string{})
	CHECK(err)
	for _, movie := range movies {
		client.Write(fmt.Sprintf("movieReview.%s", movie.MovieId), string(empty))
	}
	for i := 0; i < 1000; i++ {
		userId := fmt.Sprintf("user%d", i)
		client.Write(fmt.Sprintf("userReview.%s", userId), string(empty))
	}
}
