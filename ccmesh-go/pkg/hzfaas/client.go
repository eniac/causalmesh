package hzfaas

import (
	"context"
	"encoding/json"
	"fmt"
	. "github.com/eniac/ccmesh/pkg/common"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"time"
)

var RPCC *MeshClient = nil

type MeshGoClient struct {
	Rpcc *MeshClient
	//Id       string                   `json:"id"`
	Workload []map[string]interface{} `json:"workload"`
	Reads    []string                 `json:"reads"`
	Writes   map[string]string        `json:"writes"`
	Istail   bool                     `json:"istail"`
	Input    string                   `json:"input"`
	Low      int32                    `json:"low"`
	High     int32                    `json:"high"`
	Abort    bool                     `json:"abort"`
}

func (client *MeshGoClient) Read(k string) string {
	//start := time.Now()
	if m, ok := client.Writes[k]; ok {
		return m
	}
	res, err := (*client.Rpcc).ClientRead(context.Background(), &ClientReadRequest{Key: k, Low: client.Low, High: client.High})
	CHECK(err)
	v := res.Value
	if res.Low > client.Low {
		client.Low = res.Low
	}
	if res.High < client.High {
		client.High = res.High
	}
	if res.Abort {
		client.Abort = true
	}
	client.Reads = append(client.Reads, k)
	return v
}

func (client *MeshGoClient) Write(k string, v string) {
	start := time.Now()
	_, err := (*client.Rpcc).ClientWrite(context.Background(), &ClientWriteRequest{Key: k, Value: v})
	CHECK(err)
	client.Writes[k] = v
	fmt.Println("write time:", time.Since(start))
}

func (client *MeshGoClient) Execute() []byte {
	//fmt.Println(client.Workload)
	for _, op := range client.Workload {
		if len(op) != 1 {
			panic("op is not 1")
		}
		for k, v := range op {
			switch k {
			case "R":
				//start := time.Now()
				client.Read(v.(string))
				//fmt.Println("read time:", time.Since(start))
			case "W":
				//start := time.Now()
				vs := v.([]interface{})
				client.Writes[vs[0].(string)] = vs[1].(string)
				//client.Write(vs[0].(string), vs[1].(string))
				//fmt.Println("write time:", time.Since(start))
			}
		}
	}
	if client.Istail {
		for k, v := range client.Writes {
			client.Write(k, v)
		}
	}
	return nil
}

func CreateClient() *MeshClient {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	rpcc := NewMeshClient(conn)
	return &rpcc
}

func InitClient() {
	if RPCC == nil {
		RPCC = CreateClient()
	}
}

func Run(input []byte) []byte {
	var client MeshGoClient
	err := json.Unmarshal(input, &client)
	CHECK(err)
	//conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	//CHECK(err)
	//
	//rpcc := NewMeshClient(conn)
	InitClient()
	client.Rpcc = RPCC

	client.Execute()
	CHECK(err)
	clientStr, err := json.Marshal(client)
	CHECK(err)
	//fmt.Println(string(clientStr))
	return clientStr
}

func Test() string {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	defer conn.Close()
	c := NewMeshClient(conn)
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	r, err := c.HealthCheck(ctx, &HealthCheckRequest{})
	CHECK(err)
	return r.Status
}
