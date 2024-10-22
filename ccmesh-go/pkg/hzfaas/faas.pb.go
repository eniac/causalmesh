// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.28.1
// 	protoc        v3.15.8
// source: faas.proto

package hzfaas

import (
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
	_ "google.golang.org/protobuf/types/known/emptypb"
	reflect "reflect"
	sync "sync"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

type ClientReadRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Key  string `protobuf:"bytes,1,opt,name=key,proto3" json:"key,omitempty"`
	Low  int32  `protobuf:"varint,2,opt,name=low,proto3" json:"low,omitempty"`
	High int32  `protobuf:"varint,3,opt,name=high,proto3" json:"high,omitempty"`
}

func (x *ClientReadRequest) Reset() {
	*x = ClientReadRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ClientReadRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ClientReadRequest) ProtoMessage() {}

func (x *ClientReadRequest) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ClientReadRequest.ProtoReflect.Descriptor instead.
func (*ClientReadRequest) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{0}
}

func (x *ClientReadRequest) GetKey() string {
	if x != nil {
		return x.Key
	}
	return ""
}

func (x *ClientReadRequest) GetLow() int32 {
	if x != nil {
		return x.Low
	}
	return 0
}

func (x *ClientReadRequest) GetHigh() int32 {
	if x != nil {
		return x.High
	}
	return 0
}

type ClientReadResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Value string `protobuf:"bytes,1,opt,name=value,proto3" json:"value,omitempty"`
	Low   int32  `protobuf:"varint,2,opt,name=low,proto3" json:"low,omitempty"`
	High  int32  `protobuf:"varint,3,opt,name=high,proto3" json:"high,omitempty"`
	Abort bool   `protobuf:"varint,4,opt,name=abort,proto3" json:"abort,omitempty"`
}

func (x *ClientReadResponse) Reset() {
	*x = ClientReadResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ClientReadResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ClientReadResponse) ProtoMessage() {}

func (x *ClientReadResponse) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ClientReadResponse.ProtoReflect.Descriptor instead.
func (*ClientReadResponse) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{1}
}

func (x *ClientReadResponse) GetValue() string {
	if x != nil {
		return x.Value
	}
	return ""
}

func (x *ClientReadResponse) GetLow() int32 {
	if x != nil {
		return x.Low
	}
	return 0
}

func (x *ClientReadResponse) GetHigh() int32 {
	if x != nil {
		return x.High
	}
	return 0
}

func (x *ClientReadResponse) GetAbort() bool {
	if x != nil {
		return x.Abort
	}
	return false
}

type ClientWriteRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Key   string `protobuf:"bytes,1,opt,name=key,proto3" json:"key,omitempty"`
	Value string `protobuf:"bytes,2,opt,name=value,proto3" json:"value,omitempty"`
}

func (x *ClientWriteRequest) Reset() {
	*x = ClientWriteRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ClientWriteRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ClientWriteRequest) ProtoMessage() {}

func (x *ClientWriteRequest) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ClientWriteRequest.ProtoReflect.Descriptor instead.
func (*ClientWriteRequest) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{2}
}

func (x *ClientWriteRequest) GetKey() string {
	if x != nil {
		return x.Key
	}
	return ""
}

func (x *ClientWriteRequest) GetValue() string {
	if x != nil {
		return x.Value
	}
	return ""
}

type ClientWriteResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Ts int64 `protobuf:"varint,1,opt,name=ts,proto3" json:"ts,omitempty"`
}

func (x *ClientWriteResponse) Reset() {
	*x = ClientWriteResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ClientWriteResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ClientWriteResponse) ProtoMessage() {}

func (x *ClientWriteResponse) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ClientWriteResponse.ProtoReflect.Descriptor instead.
func (*ClientWriteResponse) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{3}
}

func (x *ClientWriteResponse) GetTs() int64 {
	if x != nil {
		return x.Ts
	}
	return 0
}

type HealthCheckRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *HealthCheckRequest) Reset() {
	*x = HealthCheckRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *HealthCheckRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*HealthCheckRequest) ProtoMessage() {}

func (x *HealthCheckRequest) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use HealthCheckRequest.ProtoReflect.Descriptor instead.
func (*HealthCheckRequest) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{4}
}

type HealthCheckResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Status string `protobuf:"bytes,1,opt,name=status,proto3" json:"status,omitempty"`
}

func (x *HealthCheckResponse) Reset() {
	*x = HealthCheckResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_faas_proto_msgTypes[5]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *HealthCheckResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*HealthCheckResponse) ProtoMessage() {}

func (x *HealthCheckResponse) ProtoReflect() protoreflect.Message {
	mi := &file_faas_proto_msgTypes[5]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use HealthCheckResponse.ProtoReflect.Descriptor instead.
func (*HealthCheckResponse) Descriptor() ([]byte, []int) {
	return file_faas_proto_rawDescGZIP(), []int{5}
}

func (x *HealthCheckResponse) GetStatus() string {
	if x != nil {
		return x.Status
	}
	return ""
}

var File_faas_proto protoreflect.FileDescriptor

var file_faas_proto_rawDesc = []byte{
	0x0a, 0x0a, 0x66, 0x61, 0x61, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x04, 0x66, 0x61,
	0x61, 0x73, 0x1a, 0x1b, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x62, 0x75, 0x66, 0x2f, 0x65, 0x6d, 0x70, 0x74, 0x79, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22,
	0x4b, 0x0a, 0x11, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x52, 0x65, 0x61, 0x64, 0x52, 0x65, 0x71,
	0x75, 0x65, 0x73, 0x74, 0x12, 0x10, 0x0a, 0x03, 0x6b, 0x65, 0x79, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x03, 0x6b, 0x65, 0x79, 0x12, 0x10, 0x0a, 0x03, 0x6c, 0x6f, 0x77, 0x18, 0x02, 0x20,
	0x01, 0x28, 0x05, 0x52, 0x03, 0x6c, 0x6f, 0x77, 0x12, 0x12, 0x0a, 0x04, 0x68, 0x69, 0x67, 0x68,
	0x18, 0x03, 0x20, 0x01, 0x28, 0x05, 0x52, 0x04, 0x68, 0x69, 0x67, 0x68, 0x22, 0x66, 0x0a, 0x12,
	0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x52, 0x65, 0x61, 0x64, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e,
	0x73, 0x65, 0x12, 0x14, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x12, 0x10, 0x0a, 0x03, 0x6c, 0x6f, 0x77, 0x18,
	0x02, 0x20, 0x01, 0x28, 0x05, 0x52, 0x03, 0x6c, 0x6f, 0x77, 0x12, 0x12, 0x0a, 0x04, 0x68, 0x69,
	0x67, 0x68, 0x18, 0x03, 0x20, 0x01, 0x28, 0x05, 0x52, 0x04, 0x68, 0x69, 0x67, 0x68, 0x12, 0x14,
	0x0a, 0x05, 0x61, 0x62, 0x6f, 0x72, 0x74, 0x18, 0x04, 0x20, 0x01, 0x28, 0x08, 0x52, 0x05, 0x61,
	0x62, 0x6f, 0x72, 0x74, 0x22, 0x3c, 0x0a, 0x12, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x57, 0x72,
	0x69, 0x74, 0x65, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x10, 0x0a, 0x03, 0x6b, 0x65,
	0x79, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x6b, 0x65, 0x79, 0x12, 0x14, 0x0a, 0x05,
	0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28, 0x09, 0x52, 0x05, 0x76, 0x61, 0x6c,
	0x75, 0x65, 0x22, 0x25, 0x0a, 0x13, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x57, 0x72, 0x69, 0x74,
	0x65, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x0e, 0x0a, 0x02, 0x74, 0x73, 0x18,
	0x01, 0x20, 0x01, 0x28, 0x03, 0x52, 0x02, 0x74, 0x73, 0x22, 0x14, 0x0a, 0x12, 0x48, 0x65, 0x61,
	0x6c, 0x74, 0x68, 0x43, 0x68, 0x65, 0x63, 0x6b, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x22,
	0x2d, 0x0a, 0x13, 0x48, 0x65, 0x61, 0x6c, 0x74, 0x68, 0x43, 0x68, 0x65, 0x63, 0x6b, 0x52, 0x65,
	0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x16, 0x0a, 0x06, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73,
	0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x06, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x32, 0xd5,
	0x01, 0x0a, 0x04, 0x4d, 0x65, 0x73, 0x68, 0x12, 0x44, 0x0a, 0x0b, 0x48, 0x65, 0x61, 0x6c, 0x74,
	0x68, 0x43, 0x68, 0x65, 0x63, 0x6b, 0x12, 0x18, 0x2e, 0x66, 0x61, 0x61, 0x73, 0x2e, 0x48, 0x65,
	0x61, 0x6c, 0x74, 0x68, 0x43, 0x68, 0x65, 0x63, 0x6b, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74,
	0x1a, 0x19, 0x2e, 0x66, 0x61, 0x61, 0x73, 0x2e, 0x48, 0x65, 0x61, 0x6c, 0x74, 0x68, 0x43, 0x68,
	0x65, 0x63, 0x6b, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x00, 0x12, 0x41, 0x0a,
	0x0a, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x52, 0x65, 0x61, 0x64, 0x12, 0x17, 0x2e, 0x66, 0x61,
	0x61, 0x73, 0x2e, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x52, 0x65, 0x61, 0x64, 0x52, 0x65, 0x71,
	0x75, 0x65, 0x73, 0x74, 0x1a, 0x18, 0x2e, 0x66, 0x61, 0x61, 0x73, 0x2e, 0x43, 0x6c, 0x69, 0x65,
	0x6e, 0x74, 0x52, 0x65, 0x61, 0x64, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x00,
	0x12, 0x44, 0x0a, 0x0b, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x57, 0x72, 0x69, 0x74, 0x65, 0x12,
	0x18, 0x2e, 0x66, 0x61, 0x61, 0x73, 0x2e, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x57, 0x72, 0x69,
	0x74, 0x65, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x19, 0x2e, 0x66, 0x61, 0x61, 0x73,
	0x2e, 0x43, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x57, 0x72, 0x69, 0x74, 0x65, 0x52, 0x65, 0x73, 0x70,
	0x6f, 0x6e, 0x73, 0x65, 0x22, 0x00, 0x42, 0x19, 0x5a, 0x17, 0x67, 0x69, 0x74, 0x68, 0x75, 0x62,
	0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x65, 0x6e, 0x69, 0x61, 0x63, 0x2f, 0x68, 0x7a, 0x66, 0x61, 0x61,
	0x73, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_faas_proto_rawDescOnce sync.Once
	file_faas_proto_rawDescData = file_faas_proto_rawDesc
)

func file_faas_proto_rawDescGZIP() []byte {
	file_faas_proto_rawDescOnce.Do(func() {
		file_faas_proto_rawDescData = protoimpl.X.CompressGZIP(file_faas_proto_rawDescData)
	})
	return file_faas_proto_rawDescData
}

var file_faas_proto_msgTypes = make([]protoimpl.MessageInfo, 6)
var file_faas_proto_goTypes = []interface{}{
	(*ClientReadRequest)(nil),   // 0: faas.ClientReadRequest
	(*ClientReadResponse)(nil),  // 1: faas.ClientReadResponse
	(*ClientWriteRequest)(nil),  // 2: faas.ClientWriteRequest
	(*ClientWriteResponse)(nil), // 3: faas.ClientWriteResponse
	(*HealthCheckRequest)(nil),  // 4: faas.HealthCheckRequest
	(*HealthCheckResponse)(nil), // 5: faas.HealthCheckResponse
}
var file_faas_proto_depIdxs = []int32{
	4, // 0: faas.Mesh.HealthCheck:input_type -> faas.HealthCheckRequest
	0, // 1: faas.Mesh.ClientRead:input_type -> faas.ClientReadRequest
	2, // 2: faas.Mesh.ClientWrite:input_type -> faas.ClientWriteRequest
	5, // 3: faas.Mesh.HealthCheck:output_type -> faas.HealthCheckResponse
	1, // 4: faas.Mesh.ClientRead:output_type -> faas.ClientReadResponse
	3, // 5: faas.Mesh.ClientWrite:output_type -> faas.ClientWriteResponse
	3, // [3:6] is the sub-list for method output_type
	0, // [0:3] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_faas_proto_init() }
func file_faas_proto_init() {
	if File_faas_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_faas_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ClientReadRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_faas_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ClientReadResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_faas_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ClientWriteRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_faas_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ClientWriteResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_faas_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*HealthCheckRequest); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_faas_proto_msgTypes[5].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*HealthCheckResponse); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_faas_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   6,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_faas_proto_goTypes,
		DependencyIndexes: file_faas_proto_depIdxs,
		MessageInfos:      file_faas_proto_msgTypes,
	}.Build()
	File_faas_proto = out.File
	file_faas_proto_rawDesc = nil
	file_faas_proto_goTypes = nil
	file_faas_proto_depIdxs = nil
}
