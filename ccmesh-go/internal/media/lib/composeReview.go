package lib

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
)

//
//func UploadUniqueId(client *GoClient, reqId string, uniqueId string) {
//	client.Write(fmt.Sprintf("compose.%s.reqId", reqId), uniqueId)
//}

func UploadText(client *GoClient, reqId string, text string) string {
	client.Write(fmt.Sprintf("compose.%s.text", reqId), text)
	return ""
}

func UploadRating(client *GoClient, reqId string, rating string) string {
	client.Write(fmt.Sprintf("compose.%s.rating", reqId), rating)
	return ""
}

func UploadUserId(client *GoClient, reqId string, userId string) string {
	client.Write(fmt.Sprintf("compose.%s.userId", reqId), userId)
	return ""
}

func UploadMovieId(client *GoClient, reqId string, movieId string) string {
	client.Write(fmt.Sprintf("compose.%s.movieId", reqId), movieId)
	return ""
}

func ComposeAndUpload(client *GoClient, reqId string) string {
	text := client.Read(fmt.Sprintf("compose.%s.text", reqId))
	rating := client.Read(fmt.Sprintf("compose.%s.rating", reqId))
	userId := client.Read(fmt.Sprintf("compose.%s.userId", reqId))
	movieId := client.Read(fmt.Sprintf("compose.%s.movieId", reqId))
	res := AnyJson{
		"text":     text,
		"rating":   rating,
		"user_id":  userId,
		"movie_id": movieId,
	}
	resStr, err := json.Marshal(res)
	CHECK(err)
	return string(resStr)
}
