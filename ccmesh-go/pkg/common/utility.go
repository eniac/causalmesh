package common

import (
	"bytes"
	"encoding/gob"
)

func DeepCopy(dist, src interface{}) {
	buf := bytes.Buffer{}
	err := gob.NewEncoder(&buf).Encode(src)
	CHECK(err)
	err = gob.NewDecoder(&buf).Decode(dist)
	CHECK(err)
}

func CHECK(err error) {
	if err != nil {
		panic(err)
	}
}
