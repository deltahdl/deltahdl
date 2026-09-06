#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

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
  Expr* init_expr = nullptr;
  std::vector<Expr*> unpacked_dims;
  std::vector<Attribute> attrs;
  // §7.2.1: for an inline aggregate (struct/union) or enum member type, the
  // full parsed type, retained so member widths can be computed by recursing
  // into nested members / enum base. Null for scalar and named-type members.
  const DataType* nested_type = nullptr;
};

struct DataType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  // §6.18: what a typedef name this type is written as was declared with, in
  // the one place the simulator can read it. EvalTypeWidth(const DataType&)
  // answers 0 for a kNamed type and every caller under src/simulator/ turns a 0
  // into 32, and the table that would resolve the name is the elaborator's and
  // never leaves it.
  //
  // The elaborator records the answer here rather than rewriting kind and
  // type_name to the bound type, because the name is what several checks are
  // about: §6.6.7 requires a nettype's resolution function to "have a return
  // type of 'T'" and reads the name to say so, and a rewritten type answers
  // that question with the struct T stands for and reports nothing. A zero
  // width means nothing was recorded, which is every type but a return type
  // ResolveNamedReturnType reached.
  uint32_t named_width = 0;
  bool named_is_signed = false;
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
  // True when the packed part was written with its range left unspecified --
  // the empty-bracket "[]" form, as in "bit []". Such a dimension has no bounds
  // to record, so neither the leading pair nor extra_packed_dims can express
  // it; this flag is what marks its presence.
  bool has_unsized_packed_dim = false;
  std::string_view type_name;
  std::string_view scope_name;
  std::string_view modport_name;
  std::string_view enum_base_name;

  DataTypeKind enum_base_kind = DataTypeKind::kImplicit;

  Expr* type_ref_expr = nullptr;
  std::vector<EnumMember> enum_members;
  std::vector<StructMember> struct_members;
  std::vector<DataType> type_params;

  // §6.20 / Syntax 8-2: when this DataType is an element of an enclosing type's
  // parameter_value_assignment given in the named form ".name(value)", this
  // holds the formal parameter name it binds to. Empty for the ordered form.
  std::string_view param_arg_name;
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
};

}  // namespace delta
