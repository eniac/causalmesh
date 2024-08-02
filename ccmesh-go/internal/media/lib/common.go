package lib

import (
	"encoding/json"
	"github.com/eniac/ccmesh/pkg/ccmesh"
	. "github.com/eniac/ccmesh/pkg/common"
	"github.com/eniac/ccmesh/pkg/hzcon"
	"github.com/eniac/ccmesh/pkg/hzfaas"
	"github.com/eniac/ccmesh/pkg/hzopt"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"strings"
)

const ALG = "opt"

//const ALG = "opt"

var MESH_RPC *ccmesh.MeshClient = nil
var CON_RPC *hzcon.MeshClient = nil
var OPT_RPC *hzopt.MeshClient = nil
var FAAS_RPC *hzfaas.MeshClient = nil

type GoClient struct {
	MeshGoClient *ccmesh.MeshGoClient
	ConGoClient  *hzcon.MeshGoClient
	OptGoClient  *hzopt.MeshGoClient
	FaasGoClient *hzfaas.MeshGoClient
}

func CreateMeshRPCC() *ccmesh.MeshClient {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	rpcc := ccmesh.NewMeshClient(conn)
	return &rpcc
}

func CreateConRPCC() *hzcon.MeshClient {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	rpcc := hzcon.NewMeshClient(conn)
	return &rpcc
}

func CreateOptRPCC() *hzopt.MeshClient {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	rpcc := hzopt.NewMeshClient(conn)
	return &rpcc
}

func CreateFaasRPCC() *hzfaas.MeshClient {
	conn, err := grpc.Dial(ADDR, grpc.WithTransportCredentials(insecure.NewCredentials()))
	CHECK(err)
	rpcc := hzfaas.NewMeshClient(conn)
	return &rpcc
}

func NewGoClient(input []byte) *GoClient {
	var client GoClient
	if ALG == "ccmesh" {
		client.MeshGoClient = &ccmesh.MeshGoClient{}
		err := json.Unmarshal(input, &client.MeshGoClient)
		CHECK(err)
		if MESH_RPC == nil {
			MESH_RPC = CreateMeshRPCC()
		}
		client.MeshGoClient.Rpcc = MESH_RPC
	} else if ALG == "con" {
		client.ConGoClient = &hzcon.MeshGoClient{}
		err := json.Unmarshal(input, &client.ConGoClient)
		CHECK(err)
		if CON_RPC == nil {
			CON_RPC = CreateConRPCC()
		}
		client.ConGoClient.Rpcc = CON_RPC
	} else if ALG == "opt" {
		client.OptGoClient = &hzopt.MeshGoClient{}
		err := json.Unmarshal(input, &client.OptGoClient)
		CHECK(err)
		if OPT_RPC == nil {
			OPT_RPC = CreateOptRPCC()
		}
		client.OptGoClient.Rpcc = OPT_RPC
	} else if ALG == "faas" {
		client.FaasGoClient = &hzfaas.MeshGoClient{}
		err := json.Unmarshal(input, &client.FaasGoClient)
		CHECK(err)
		if FAAS_RPC == nil {
			FAAS_RPC = CreateFaasRPCC()
		}
		client.FaasGoClient.Rpcc = FAAS_RPC
	} else {
		panic("unknown algorithm")
	}
	return &client
}

func SeGoClient(client *GoClient) []byte {
	var clientStr []byte
	var err error
	if ALG == "ccmesh" {
		clientStr, err = json.Marshal(client.MeshGoClient)
	} else if ALG == "con" {
		clientStr, err = json.Marshal(client.ConGoClient)
	} else if ALG == "opt" {
		clientStr, err = json.Marshal(client.OptGoClient)
	} else if ALG == "faas" {
		clientStr, err = json.Marshal(client.FaasGoClient)
	} else {
		panic("unknown algorithm")
	}
	CHECK(err)
	return clientStr
}

func (client *GoClient) GetInput() string {
	if ALG == "ccmesh" {
		return client.MeshGoClient.Input
	} else if ALG == "con" {
		return client.ConGoClient.Input
	} else if ALG == "opt" {
		return client.OptGoClient.Input
	} else if ALG == "faas" {
		return client.FaasGoClient.Input
	} else {
		panic("unknown algorithm")
	}
}

func (client *GoClient) SetInput(input string) {
	if ALG == "ccmesh" {
		client.MeshGoClient.Input = input
	} else if ALG == "con" {
		client.ConGoClient.Input = input
	} else if ALG == "opt" {
		client.OptGoClient.Input = input
	} else if ALG == "faas" {
		client.FaasGoClient.Input = input
	} else {
		panic("unknown algorithm")
	}
}

func (client *GoClient) Read(k string) string {
	if ALG == "ccmesh" {
		return client.MeshGoClient.Read(k)
	} else if ALG == "con" {
		return client.ConGoClient.Read(k)
	} else if ALG == "opt" {
		return client.OptGoClient.Read(k)
	} else if ALG == "faas" {
		return client.FaasGoClient.Read(k)
	} else {
		panic("unknown algorithm")
	}
}

func (client *GoClient) Write(k string, v string) {
	if ALG == "ccmesh" {
		if strings.HasPrefix(k, "compose") {
			client.MeshGoClient.Local[k] = &Meta{Key: k, Value: v, Vc: VC{}, Deps: map[string]VC{}}
			return
		}
		client.MeshGoClient.Write(k, v)
	} else if ALG == "con" {
		client.ConGoClient.Writes[k] = v
		//client.ConGoClient.Write(k, v)
	} else if ALG == "opt" {
		client.OptGoClient.Writes[k] = v
		//client.OptGoClient.Write(k, v)
	} else if ALG == "faas" {
		client.FaasGoClient.Writes[k] = v
		//client.OptGoClient.Write(k, v)
	} else {
		panic("unknown algorithm")
	}
}

func (client *GoClient) Finish() {
	if ALG == "ccmesh" {
	} else if ALG == "con" {
		if client.ConGoClient.Istail {
			for k, v := range client.ConGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if strings.HasPrefix(k, "reviewStorage") {
					client.ConGoClient.Write(k, v)
				}
			}
			for k, v := range client.ConGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if !strings.HasPrefix(k, "reviewStorage") {
					client.ConGoClient.Write(k, v)
				}
			}
		}
	} else if ALG == "opt" {
		if client.OptGoClient.Istail {
			for k, v := range client.OptGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if strings.HasPrefix(k, "reviewStorage") {
					client.OptGoClient.Write(k, v)
				}
			}
			for k, v := range client.OptGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if !strings.HasPrefix(k, "reviewStorage") {
					client.OptGoClient.Write(k, v)
				}
			}
		}
	} else if ALG == "faas" {
		if client.FaasGoClient.Istail {
			for k, v := range client.FaasGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if strings.HasPrefix(k, "reviewStorage") {
					client.FaasGoClient.Write(k, v)
				}
			}
			for k, v := range client.FaasGoClient.Writes {
				if strings.HasPrefix(k, "compose") {
					continue
				}
				if !strings.HasPrefix(k, "reviewStorage") {
					client.FaasGoClient.Write(k, v)
				}
			}
		}
	} else {
		panic("unknown algorithm")
	}
}
