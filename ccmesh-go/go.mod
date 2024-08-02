module github.com/eniac/ccmesh

go 1.17

require (
	cs.utexas.edu/zjia/faas v0.0.0
	github.com/golang/protobuf v1.5.4
	golang.org/x/net v0.0.0-20201021035429-f5854403a974 // indirect
	golang.org/x/sys v0.0.0-20210119212857-b64e53b001e4 // indirect
	golang.org/x/text v0.3.3 // indirect
	google.golang.org/genproto v0.0.0-20200526211855-cb27e3aa2013 // indirect
	google.golang.org/grpc v1.49.0
	google.golang.org/protobuf v1.33.0
)

require (
	github.com/gomodule/redigo v1.8.9
	github.com/stretchr/testify v1.8.0
)

require (
	github.com/davecgh/go-spew v1.1.1 // indirect
	github.com/pmezard/go-difflib v1.0.0 // indirect
	gopkg.in/yaml.v3 v3.0.1 // indirect
)

replace cs.utexas.edu/zjia/faas => ../nightcore/worker/golang
