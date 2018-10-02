// Code generated by protoc-gen-go. DO NOT EDIT.
// source: cblocks.proto

package cbservice

import proto "github.com/golang/protobuf/proto"
import fmt "fmt"
import math "math"

import (
	context "golang.org/x/net/context"
	grpc "google.golang.org/grpc"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.ProtoPackageIsVersion2 // please upgrade the proto package

type LieAlgebra_LieType int32

const (
	LieAlgebra_A LieAlgebra_LieType = 0
	LieAlgebra_B LieAlgebra_LieType = 1
	LieAlgebra_C LieAlgebra_LieType = 2
	LieAlgebra_D LieAlgebra_LieType = 3
)

var LieAlgebra_LieType_name = map[int32]string{
	0: "A",
	1: "B",
	2: "C",
	3: "D",
}
var LieAlgebra_LieType_value = map[string]int32{
	"A": 0,
	"B": 1,
	"C": 2,
	"D": 3,
}

func (x LieAlgebra_LieType) String() string {
	return proto.EnumName(LieAlgebra_LieType_name, int32(x))
}
func (LieAlgebra_LieType) EnumDescriptor() ([]byte, []int) {
	return fileDescriptor_cblocks_5e0bc0434e8a128e, []int{1, 0}
}

type SymConformalBlocksRequest struct {
	Algebra              *LieAlgebra `protobuf:"bytes,1,opt,name=algebra,proto3" json:"algebra,omitempty"`
	Weight               *Weight     `protobuf:"bytes,2,opt,name=weight,proto3" json:"weight,omitempty"`
	NumPoints            int64       `protobuf:"varint,3,opt,name=num_points,json=numPoints,proto3" json:"num_points,omitempty"`
	Level                int64       `protobuf:"varint,4,opt,name=level,proto3" json:"level,omitempty"`
	XXX_NoUnkeyedLiteral struct{}    `json:"-"`
	XXX_unrecognized     []byte      `json:"-"`
	XXX_sizecache        int32       `json:"-"`
}

func (m *SymConformalBlocksRequest) Reset()         { *m = SymConformalBlocksRequest{} }
func (m *SymConformalBlocksRequest) String() string { return proto.CompactTextString(m) }
func (*SymConformalBlocksRequest) ProtoMessage()    {}
func (*SymConformalBlocksRequest) Descriptor() ([]byte, []int) {
	return fileDescriptor_cblocks_5e0bc0434e8a128e, []int{0}
}
func (m *SymConformalBlocksRequest) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_SymConformalBlocksRequest.Unmarshal(m, b)
}
func (m *SymConformalBlocksRequest) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_SymConformalBlocksRequest.Marshal(b, m, deterministic)
}
func (dst *SymConformalBlocksRequest) XXX_Merge(src proto.Message) {
	xxx_messageInfo_SymConformalBlocksRequest.Merge(dst, src)
}
func (m *SymConformalBlocksRequest) XXX_Size() int {
	return xxx_messageInfo_SymConformalBlocksRequest.Size(m)
}
func (m *SymConformalBlocksRequest) XXX_DiscardUnknown() {
	xxx_messageInfo_SymConformalBlocksRequest.DiscardUnknown(m)
}

var xxx_messageInfo_SymConformalBlocksRequest proto.InternalMessageInfo

func (m *SymConformalBlocksRequest) GetAlgebra() *LieAlgebra {
	if m != nil {
		return m.Algebra
	}
	return nil
}

func (m *SymConformalBlocksRequest) GetWeight() *Weight {
	if m != nil {
		return m.Weight
	}
	return nil
}

func (m *SymConformalBlocksRequest) GetNumPoints() int64 {
	if m != nil {
		return m.NumPoints
	}
	return 0
}

func (m *SymConformalBlocksRequest) GetLevel() int64 {
	if m != nil {
		return m.Level
	}
	return 0
}

type LieAlgebra struct {
	Type                 LieAlgebra_LieType `protobuf:"varint,1,opt,name=type,proto3,enum=cbservice.LieAlgebra_LieType" json:"type,omitempty"`
	Rank                 int64              `protobuf:"varint,2,opt,name=rank,proto3" json:"rank,omitempty"`
	XXX_NoUnkeyedLiteral struct{}           `json:"-"`
	XXX_unrecognized     []byte             `json:"-"`
	XXX_sizecache        int32              `json:"-"`
}

func (m *LieAlgebra) Reset()         { *m = LieAlgebra{} }
func (m *LieAlgebra) String() string { return proto.CompactTextString(m) }
func (*LieAlgebra) ProtoMessage()    {}
func (*LieAlgebra) Descriptor() ([]byte, []int) {
	return fileDescriptor_cblocks_5e0bc0434e8a128e, []int{1}
}
func (m *LieAlgebra) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_LieAlgebra.Unmarshal(m, b)
}
func (m *LieAlgebra) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_LieAlgebra.Marshal(b, m, deterministic)
}
func (dst *LieAlgebra) XXX_Merge(src proto.Message) {
	xxx_messageInfo_LieAlgebra.Merge(dst, src)
}
func (m *LieAlgebra) XXX_Size() int {
	return xxx_messageInfo_LieAlgebra.Size(m)
}
func (m *LieAlgebra) XXX_DiscardUnknown() {
	xxx_messageInfo_LieAlgebra.DiscardUnknown(m)
}

var xxx_messageInfo_LieAlgebra proto.InternalMessageInfo

func (m *LieAlgebra) GetType() LieAlgebra_LieType {
	if m != nil {
		return m.Type
	}
	return LieAlgebra_A
}

func (m *LieAlgebra) GetRank() int64 {
	if m != nil {
		return m.Rank
	}
	return 0
}

// An integral weight
type Weight struct {
	Coords               []int64  `protobuf:"varint,1,rep,packed,name=coords,proto3" json:"coords,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *Weight) Reset()         { *m = Weight{} }
func (m *Weight) String() string { return proto.CompactTextString(m) }
func (*Weight) ProtoMessage()    {}
func (*Weight) Descriptor() ([]byte, []int) {
	return fileDescriptor_cblocks_5e0bc0434e8a128e, []int{2}
}
func (m *Weight) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_Weight.Unmarshal(m, b)
}
func (m *Weight) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_Weight.Marshal(b, m, deterministic)
}
func (dst *Weight) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Weight.Merge(dst, src)
}
func (m *Weight) XXX_Size() int {
	return xxx_messageInfo_Weight.Size(m)
}
func (m *Weight) XXX_DiscardUnknown() {
	xxx_messageInfo_Weight.DiscardUnknown(m)
}

var xxx_messageInfo_Weight proto.InternalMessageInfo

func (m *Weight) GetCoords() []int64 {
	if m != nil {
		return m.Coords
	}
	return nil
}

// A integer reply message
type IntReply struct {
	Result               int64    `protobuf:"varint,1,opt,name=result,proto3" json:"result,omitempty"`
	BigResult            string   `protobuf:"bytes,2,opt,name=big_result,json=bigResult,proto3" json:"big_result,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *IntReply) Reset()         { *m = IntReply{} }
func (m *IntReply) String() string { return proto.CompactTextString(m) }
func (*IntReply) ProtoMessage()    {}
func (*IntReply) Descriptor() ([]byte, []int) {
	return fileDescriptor_cblocks_5e0bc0434e8a128e, []int{3}
}
func (m *IntReply) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_IntReply.Unmarshal(m, b)
}
func (m *IntReply) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_IntReply.Marshal(b, m, deterministic)
}
func (dst *IntReply) XXX_Merge(src proto.Message) {
	xxx_messageInfo_IntReply.Merge(dst, src)
}
func (m *IntReply) XXX_Size() int {
	return xxx_messageInfo_IntReply.Size(m)
}
func (m *IntReply) XXX_DiscardUnknown() {
	xxx_messageInfo_IntReply.DiscardUnknown(m)
}

var xxx_messageInfo_IntReply proto.InternalMessageInfo

func (m *IntReply) GetResult() int64 {
	if m != nil {
		return m.Result
	}
	return 0
}

func (m *IntReply) GetBigResult() string {
	if m != nil {
		return m.BigResult
	}
	return ""
}

func init() {
	proto.RegisterType((*SymConformalBlocksRequest)(nil), "cbservice.SymConformalBlocksRequest")
	proto.RegisterType((*LieAlgebra)(nil), "cbservice.LieAlgebra")
	proto.RegisterType((*Weight)(nil), "cbservice.Weight")
	proto.RegisterType((*IntReply)(nil), "cbservice.IntReply")
	proto.RegisterEnum("cbservice.LieAlgebra_LieType", LieAlgebra_LieType_name, LieAlgebra_LieType_value)
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConn

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion4

// CBlocksClient is the client API for CBlocks service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type CBlocksClient interface {
	// Computes the sum of the coordinates of a weight
	Sum(ctx context.Context, in *Weight, opts ...grpc.CallOption) (*IntReply, error)
	// Computes the rank of the conformal blocks bundle
	ComputeRank(ctx context.Context, in *SymConformalBlocksRequest, opts ...grpc.CallOption) (*IntReply, error)
}

type cBlocksClient struct {
	cc *grpc.ClientConn
}

func NewCBlocksClient(cc *grpc.ClientConn) CBlocksClient {
	return &cBlocksClient{cc}
}

func (c *cBlocksClient) Sum(ctx context.Context, in *Weight, opts ...grpc.CallOption) (*IntReply, error) {
	out := new(IntReply)
	err := c.cc.Invoke(ctx, "/cbservice.CBlocks/Sum", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *cBlocksClient) ComputeRank(ctx context.Context, in *SymConformalBlocksRequest, opts ...grpc.CallOption) (*IntReply, error) {
	out := new(IntReply)
	err := c.cc.Invoke(ctx, "/cbservice.CBlocks/ComputeRank", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// CBlocksServer is the server API for CBlocks service.
type CBlocksServer interface {
	// Computes the sum of the coordinates of a weight
	Sum(context.Context, *Weight) (*IntReply, error)
	// Computes the rank of the conformal blocks bundle
	ComputeRank(context.Context, *SymConformalBlocksRequest) (*IntReply, error)
}

func RegisterCBlocksServer(s *grpc.Server, srv CBlocksServer) {
	s.RegisterService(&_CBlocks_serviceDesc, srv)
}

func _CBlocks_Sum_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(Weight)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(CBlocksServer).Sum(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/cbservice.CBlocks/Sum",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(CBlocksServer).Sum(ctx, req.(*Weight))
	}
	return interceptor(ctx, in, info, handler)
}

func _CBlocks_ComputeRank_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(SymConformalBlocksRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(CBlocksServer).ComputeRank(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/cbservice.CBlocks/ComputeRank",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(CBlocksServer).ComputeRank(ctx, req.(*SymConformalBlocksRequest))
	}
	return interceptor(ctx, in, info, handler)
}

var _CBlocks_serviceDesc = grpc.ServiceDesc{
	ServiceName: "cbservice.CBlocks",
	HandlerType: (*CBlocksServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "Sum",
			Handler:    _CBlocks_Sum_Handler,
		},
		{
			MethodName: "ComputeRank",
			Handler:    _CBlocks_ComputeRank_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "cblocks.proto",
}

func init() { proto.RegisterFile("cblocks.proto", fileDescriptor_cblocks_5e0bc0434e8a128e) }

var fileDescriptor_cblocks_5e0bc0434e8a128e = []byte{
	// 351 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x74, 0x92, 0xc1, 0x4e, 0xe3, 0x30,
	0x10, 0x86, 0x9b, 0xa6, 0x4d, 0x37, 0x53, 0xed, 0x2a, 0xeb, 0x5d, 0x50, 0x40, 0xaa, 0x54, 0x45,
	0x20, 0xc1, 0xa5, 0x88, 0xf2, 0x04, 0x6d, 0xb8, 0x80, 0x38, 0x20, 0x17, 0x89, 0x63, 0x95, 0x84,
	0xa1, 0x44, 0x75, 0xe2, 0xe0, 0x38, 0x45, 0xe5, 0x01, 0x78, 0x1a, 0x1e, 0x12, 0xdb, 0x49, 0xa1,
	0x12, 0xf4, 0x34, 0x9e, 0x7f, 0xbe, 0x78, 0xfe, 0xf1, 0x04, 0x7e, 0x27, 0x31, 0xe3, 0xc9, 0xb2,
	0x1c, 0x15, 0x82, 0x4b, 0x4e, 0xdc, 0x24, 0x2e, 0x51, 0xac, 0xd2, 0x04, 0x83, 0x77, 0x0b, 0x0e,
	0x66, 0xeb, 0x2c, 0xe4, 0xf9, 0x23, 0x17, 0x59, 0xc4, 0xa6, 0x86, 0xa3, 0xf8, 0x5c, 0x61, 0x29,
	0xc9, 0x19, 0xf4, 0x22, 0xb6, 0xc0, 0x58, 0x44, 0xbe, 0x35, 0xb4, 0x4e, 0xfa, 0xe3, 0xbd, 0xd1,
	0xe7, 0xa7, 0xa3, 0x9b, 0x14, 0x27, 0x75, 0x91, 0x6e, 0x28, 0x72, 0x0a, 0xce, 0x0b, 0xa6, 0x8b,
	0x27, 0xe9, 0xb7, 0x0d, 0xff, 0x77, 0x8b, 0xbf, 0x37, 0x05, 0xda, 0x00, 0x64, 0x00, 0x90, 0x57,
	0xd9, 0xbc, 0xe0, 0x69, 0x2e, 0x4b, 0xdf, 0x56, 0xb8, 0x4d, 0x5d, 0xa5, 0xdc, 0x1a, 0x81, 0xfc,
	0x87, 0x2e, 0xc3, 0x15, 0x32, 0xbf, 0x63, 0x2a, 0x75, 0x12, 0xbc, 0x02, 0x7c, 0xb5, 0x25, 0xe7,
	0xd0, 0x91, 0xeb, 0x02, 0x8d, 0xb7, 0x3f, 0xe3, 0xc1, 0x8f, 0xde, 0xf4, 0xf1, 0x4e, 0x41, 0xd4,
	0xa0, 0x84, 0x40, 0x47, 0x44, 0xf9, 0xd2, 0xd8, 0xb3, 0xa9, 0x39, 0x07, 0xc7, 0xd0, 0x6b, 0x20,
	0xd2, 0x05, 0x6b, 0xe2, 0xb5, 0x74, 0x98, 0x7a, 0x96, 0x0e, 0xa1, 0xd7, 0xd6, 0xe1, 0xd2, 0xb3,
	0x83, 0x21, 0x38, 0xf5, 0x08, 0x64, 0x1f, 0x9c, 0x84, 0x73, 0xf1, 0x50, 0xaa, 0xce, 0xb6, 0xba,
	0xa6, 0xc9, 0x82, 0x09, 0xfc, 0xba, 0xca, 0x25, 0xc5, 0x82, 0xad, 0x35, 0x23, 0xb0, 0xac, 0x98,
	0x34, 0xee, 0x14, 0x53, 0x67, 0x7a, 0xec, 0x38, 0x5d, 0xcc, 0x9b, 0x9a, 0xb6, 0xe1, 0x52, 0x57,
	0x29, 0xd4, 0x08, 0xe3, 0x37, 0x0b, 0x7a, 0x61, 0xbd, 0x04, 0xf5, 0xfa, 0xf6, 0xac, 0xca, 0xc8,
	0xf7, 0x37, 0x3c, 0xfc, 0xb7, 0x25, 0x6d, 0x3a, 0x06, 0x2d, 0x72, 0x0d, 0xfd, 0x90, 0x67, 0x45,
	0x25, 0x91, 0xaa, 0xb9, 0xc8, 0xd1, 0x16, 0xb5, 0x73, 0xc7, 0x3b, 0xee, 0x8a, 0x1d, 0xf3, 0xab,
	0x5c, 0x7c, 0x04, 0x00, 0x00, 0xff, 0xff, 0x63, 0x32, 0x1d, 0x8d, 0x3b, 0x02, 0x00, 0x00,
}
