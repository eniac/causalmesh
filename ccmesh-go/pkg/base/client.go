package base

import (
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
	"github.com/gomodule/redigo/redis"
	"strconv"
	"time"
)

var POOL *redis.Pool = nil

type BaseGoClient struct {
	pool     *redis.Pool
	Workload []map[string]interface{} `json:"workload"`
}

func (client *BaseGoClient) Read(k string) string {
	pool := client.pool.Get()
	defer pool.Close()
	value, err := pool.Do("GET", k)
	CHECK(err)
	res := fmt.Sprintf("%s", value)
	return res
}

func (client *BaseGoClient) Write(k string, v string) {
	pool := client.pool.Get()
	defer pool.Close()
	vint, err := strconv.Atoi(v)
	CHECK(err)
	_, err = pool.Do("SET", k, fmt.Sprintf("%08d", vint))
	CHECK(err)
}

func (client *BaseGoClient) Execute() []byte {
	for _, op := range client.Workload {
		if len(op) != 1 {
			panic("op is not 1")
		}
		for k, v := range op {
			switch k {
			case "R":
				//start := time.Now()
				time.Sleep(5 * time.Millisecond)
				client.Read(v.(string))
				//fmt.Println("read time:", time.Since(start))
			case "W":
				//start := time.Now()
				vs := v.([]interface{})
				time.Sleep(5 * time.Millisecond)
				client.Write(vs[0].(string), vs[1].(string))
				//fmt.Println("write time:", time.Since(start))
			}
		}
	}
	return nil
}

func CreatePool() *redis.Pool {
	return &redis.Pool{
		MaxIdle:   80,
		MaxActive: 12000,
		Dial: func() (redis.Conn, error) {
			c, err := redis.Dial("tcp", "10.10.1.2:6379")
			if err != nil {
				panic(err.Error())
			}
			return c, err
		},
	}
}

func InitPool() {
	if POOL == nil {
		POOL = CreatePool()
	}
}

func Run(input []byte) []byte {
	fmt.Println("base client run")
	var client BaseGoClient
	err := json.Unmarshal(input, &client)
	CHECK(err)
	InitPool()
	client.pool = POOL

	client.Execute()
	CHECK(err)
	clientStr, err := json.Marshal(client)
	CHECK(err)
	//fmt.Println(string(clientStr))
	return clientStr
}
