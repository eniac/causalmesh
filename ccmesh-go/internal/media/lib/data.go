package lib

type User struct {
	UserId    string
	FirstName string
	LastName  string
	Username  string
	Password  string
	Salt      string
}

type Review struct {
	ReviewId string `json:"review_id"`
	UserId   string `json:"user_id"`
	//ReqId    string `json:"req_id"`
	Text    string `json:"text"`
	MovieId string `json:"movie_id"`
	Rating  string `json:"rating"`
}

type CastInfo struct {
	CastInfoId string
	Name       string
	Gender     bool
	Intro      string
}

type Cast struct {
	CastId     string
	Character  string
	CastInfoId string
}

type MovieInfo struct {
	MovieId      string
	Title        string
	Casts        []Cast
	PlotId       string
	ThumbnailIds []string
	PhotoIds     []string
	VideoIds     []string
	AvgRating    float64
	NumRating    int32
}

type ReviewInfo struct {
	ReviewId  string
	Timestamp string
}

type Page struct {
	MovieInfo MovieInfo
	Reviews   []Review
	CastInfos []CastInfo
	Plot      string
}
