// Code generated by protoc-gen-go-grpc. DO NOT EDIT.
// versions:
// - protoc-gen-go-grpc v1.2.0
// - protoc             v3.15.8
// source: faas.proto

package hzfaas

import (
	context "context"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
)

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
// Requires gRPC-Go v1.32.0 or later.
const _ = grpc.SupportPackageIsVersion7

// MeshClient is the client API for Mesh service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://pkg.go.dev/google.golang.org/grpc/?tab=doc#ClientConn.NewStream.
type MeshClient interface {
	HealthCheck(ctx context.Context, in *HealthCheckRequest, opts ...grpc.CallOption) (*HealthCheckResponse, error)
	ClientRead(ctx context.Context, in *ClientReadRequest, opts ...grpc.CallOption) (*ClientReadResponse, error)
	ClientWrite(ctx context.Context, in *ClientWriteRequest, opts ...grpc.CallOption) (*ClientWriteResponse, error)
}

type meshClient struct {
	cc grpc.ClientConnInterface
}

func NewMeshClient(cc grpc.ClientConnInterface) MeshClient {
	return &meshClient{cc}
}

func (c *meshClient) HealthCheck(ctx context.Context, in *HealthCheckRequest, opts ...grpc.CallOption) (*HealthCheckResponse, error) {
	out := new(HealthCheckResponse)
	err := c.cc.Invoke(ctx, "/faas.Mesh/HealthCheck", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *meshClient) ClientRead(ctx context.Context, in *ClientReadRequest, opts ...grpc.CallOption) (*ClientReadResponse, error) {
	out := new(ClientReadResponse)
	err := c.cc.Invoke(ctx, "/faas.Mesh/ClientRead", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *meshClient) ClientWrite(ctx context.Context, in *ClientWriteRequest, opts ...grpc.CallOption) (*ClientWriteResponse, error) {
	out := new(ClientWriteResponse)
	err := c.cc.Invoke(ctx, "/faas.Mesh/ClientWrite", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// MeshServer is the server API for Mesh service.
// All implementations must embed UnimplementedMeshServer
// for forward compatibility
type MeshServer interface {
	HealthCheck(context.Context, *HealthCheckRequest) (*HealthCheckResponse, error)
	ClientRead(context.Context, *ClientReadRequest) (*ClientReadResponse, error)
	ClientWrite(context.Context, *ClientWriteRequest) (*ClientWriteResponse, error)
	mustEmbedUnimplementedMeshServer()
}

// UnimplementedMeshServer must be embedded to have forward compatible implementations.
type UnimplementedMeshServer struct {
}

func (UnimplementedMeshServer) HealthCheck(context.Context, *HealthCheckRequest) (*HealthCheckResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method HealthCheck not implemented")
}
func (UnimplementedMeshServer) ClientRead(context.Context, *ClientReadRequest) (*ClientReadResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method ClientRead not implemented")
}
func (UnimplementedMeshServer) ClientWrite(context.Context, *ClientWriteRequest) (*ClientWriteResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method ClientWrite not implemented")
}
func (UnimplementedMeshServer) mustEmbedUnimplementedMeshServer() {}

// UnsafeMeshServer may be embedded to opt out of forward compatibility for this service.
// Use of this interface is not recommended, as added methods to MeshServer will
// result in compilation errors.
type UnsafeMeshServer interface {
	mustEmbedUnimplementedMeshServer()
}

func RegisterMeshServer(s grpc.ServiceRegistrar, srv MeshServer) {
	s.RegisterService(&Mesh_ServiceDesc, srv)
}

func _Mesh_HealthCheck_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(HealthCheckRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(MeshServer).HealthCheck(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/faas.Mesh/HealthCheck",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(MeshServer).HealthCheck(ctx, req.(*HealthCheckRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Mesh_ClientRead_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ClientReadRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(MeshServer).ClientRead(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/faas.Mesh/ClientRead",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(MeshServer).ClientRead(ctx, req.(*ClientReadRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _Mesh_ClientWrite_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(ClientWriteRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(MeshServer).ClientWrite(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/faas.Mesh/ClientWrite",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(MeshServer).ClientWrite(ctx, req.(*ClientWriteRequest))
	}
	return interceptor(ctx, in, info, handler)
}

// Mesh_ServiceDesc is the grpc.ServiceDesc for Mesh service.
// It's only intended for direct use with grpc.RegisterService,
// and not to be introspected or modified (even as a copy)
var Mesh_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "faas.Mesh",
	HandlerType: (*MeshServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "HealthCheck",
			Handler:    _Mesh_HealthCheck_Handler,
		},
		{
			MethodName: "ClientRead",
			Handler:    _Mesh_ClientRead_Handler,
		},
		{
			MethodName: "ClientWrite",
			Handler:    _Mesh_ClientWrite_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "faas.proto",
}