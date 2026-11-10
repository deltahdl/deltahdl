#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"

namespace delta {

enum class Direction : uint8_t {
  kNone,
  kInput,
  kOutput,
  kInout,
  kRef,
};

enum class DataTypeKind : uint8_t {
  kImplicit,
  kLogic,
  kReg,
  kBit,
  kByte,
  kShortint,
  kInt,
  kLongint,
  kInteger,
  kReal,
  kShortreal,
  kTime,
  kRealtime,
  kString,
  kVoid,
  kNamed,
  kEnum,
  kStruct,
  kUnion,
  kEvent,
  kChandle,
  kWire,
  kTri,
  kWand,
  kWor,
  kTriand,
  kTrior,
  kTri0,
  kTri1,
  kTrireg,
  kSupply0,
  kSupply1,
  kUwire,
  kVirtualInterface,
};

struct EnumMember {
  std::string_view name;
  Expr* value = nullptr;
  Expr* range_start = nullptr;
  Expr* range_end = nullptr;
};

struct DataType;

struct StructMember {
  DataTypeKind type_kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool is_rand = false;
  bool is_randc = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> extra_packed_dims;
  std::string_view name;
  std::string_view type_name;
  std::string_view scope_name;
  Expr* init_expr = nullptr;
  std::vector<Expr*> unpacked_dims;
  std::vector<Attribute> attrs;
  const DataType* nested_type = nullptr;
  uint32_t resolved_width = 0;
  std::vector<DataType> type_params;
};

struct DataType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool signing_written = false;
  bool is_packed = false;
  bool is_const = false;
  bool is_net = false;
  bool is_interconnect = false;
  bool is_tagged = false;
  bool is_soft = false;
  bool is_vectored = false;
  bool is_scalared = false;
  uint8_t charge_strength = 0;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::vector<std::pair<Expr*, Expr*>> extra_packed_dims;
  bool has_unsized_packed_dim = false;
  std::string_view type_name;
  std::string_view scope_name;
  std::vector<std::string_view> outer_scope_names;
  bool scope_param_assignment_written = false;
  std::string_view modport_name;
  std::string_view enum_base_name;

  DataTypeKind enum_base_kind = DataTypeKind::kImplicit;
  std::vector<std::pair<Expr*, Expr*>> enum_array_dims;

  Expr* type_ref_expr = nullptr;
  std::vector<EnumMember> enum_members;
  std::vector<StructMember> struct_members;
  std::vector<DataType> type_params;

  std::string_view param_arg_name;

  SourceLoc decl_loc;

  DataTypeKind net_keyword = DataTypeKind::kImplicit;

  bool names_unpacked_array = false;

  bool param_assignment_written = false;
  std::vector<DataType> specialized_scopes;
};

struct FunctionArg {
  Direction direction = Direction::kNone;
  bool is_const = false;
  bool is_ref_static = false;
  bool is_default = false;
  DataType data_type;
  std::string_view name;
  Expr* default_value = nullptr;
  std::vector<Expr*> unpacked_dims;
  bool is_untyped = false;
};

}  // namespace delta
