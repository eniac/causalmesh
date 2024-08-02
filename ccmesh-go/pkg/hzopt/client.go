package hzopt

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
	Rpcc     *MeshClient
	Id       string                   `json:"id"`
	Workload []map[string]interface{} `json:"workload"`
	Deps     map[string]VC            `json:"deps"`
	Writes   map[string]string        `json:"writes"`
	Istail   bool                     `json:"istail"`
	Input    string                   `json:"input"`
}

func (client *MeshGoClient) Read(k string) string {
	start := time.Now()
	if m, ok := client.Writes[k]; ok {
		return m
	}
	res, err := (*client.Rpcc).ClientRead(context.Background(), &ClientReadRequest{Id: client.Id, Key: k})
	CHECK(err)
	var vc VC
	err = json.Unmarshal([]byte(res.Vc), &vc)
	CHECK(err)
	InsertOrMergeVC(&client.Deps, k, &vc)
	fmt.Println("read", k, ": ", vc, " time:", time.Since(start))
	return res.Value
}

func (client *MeshGoClient) Write(k string, v string) {
	start := time.Now()
	depsStr, err := json.Marshal(client.Deps)
	CHECK(err)
	res, err := (*client.Rpcc).ClientWrite(context.Background(), &ClientWriteRequest{Key: k, Value: v, Deps: string(depsStr)})
	CHECK(err)
	var vc VC
	err = json.Unmarshal([]byte(res.Vc), &vc)
	CHECK(err)
	InsertOrMergeVC(&client.Deps, k, &vc)
	fmt.Println("write time:", time.Since(start))
}

func (client *MeshGoClient) Execute() []byte {
	if client.Deps == nil {
		panic("client not init")
	}
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
