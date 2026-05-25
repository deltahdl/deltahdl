#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;
  std::string_view string_value;
};

enum class RtlirNodeKind : uint8_t {
  kModule,
  kPort,
  kNet,
  kVariable,
  kContAssign,
  kProcess,
  kParamDecl,
  kModuleInst,
};

enum class RtlirProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
  kFinal,
};

struct RtlirPort {
  std::string_view name;
  Direction direction;
  DataTypeKind type_kind;
  uint32_t width = 1;
  bool is_signed = false;
  bool is_var = false;
  bool is_interconnect = false;
  bool is_interface_port = false;
  std::string_view interface_type_name;
  Expr* default_value = nullptr;
  std::vector<ResolvedAttribute> attrs;
  uint32_t num_unpacked_dims = 0;
  std::vector<uint32_t> unpacked_dim_sizes;
};

struct RtlirNet {
  std::string_view name;
  NetType net_type = NetType::kWire;
  uint32_t width = 1;

  bool is_signed = false;
  std::vector<uint32_t> driver_indices;

  Strength charge_strength = Strength::kMedium;
  uint32_t trireg_capacitance = 0;
  uint64_t decay_ticks = 0;

  bool is_vectored = false;
  bool is_scalared = false;

  bool is_user_nettype = false;
  std::string_view resolve_func;

  std::string_view nettype_name;
  std::vector<ResolvedAttribute> attrs;
};

struct RtlirVariable {
  std::string_view name;
  uint32_t width = 1;
  bool is_4state = true;
  bool is_event = false;
  bool is_string = false;
  bool is_real = false;
  bool is_signed = false;
  bool is_chandle = false;
  const Expr* init_expr = nullptr;
  const DataType* dtype = nullptr;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  uint32_t unpacked_size = 0;
  uint32_t unpacked_lo = 0;
  bool is_descending = false;
  bool is_dynamic = false;
  bool is_queue = false;
  int32_t queue_max_size = -1;
  bool is_assoc = false;
  bool is_string_index = false;
  bool is_wildcard_index = false;
  bool is_class_index = false;
  // Signedness of an integral associative-array index type. Determines whether
  // an index expression is sign- or zero-extended to the index width and the
  // resulting key ordering (§7.8.4). Built-in integral index types are signed.
  bool is_index_signed = true;
  uint32_t assoc_index_width = 32;
  std::string_view assoc_index_class_name;
  std::string_view class_type_name;
  std::string_view enum_type_name;
  std::vector<ResolvedAttribute> attrs;
};

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  uint32_t width = 0;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* delay_decay = nullptr;

  bool from_nonresistive_switch = false;

  bool from_resistive_switch = false;

  Expr* data_input = nullptr;
  std::vector<ResolvedAttribute> attrs;
};

struct RtlirAlias {
  std::vector<Expr*> nets;
};

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
};

struct RtlirParamDecl {
  std::string_view name;
  Expr* default_value = nullptr;
  int64_t resolved_value = 0;
  bool is_resolved = false;
  bool is_localparam = false;
  bool from_override = false;
  bool is_unbounded = false;
  bool is_type_param = false;

  uint32_t decl_width = 0;
  bool decl_is_signed = false;
  bool has_decl_type = false;
  bool has_decl_range = false;
};

struct RtlirPortBinding {
  std::string_view port_name;
  Direction direction;
  Expr* connection = nullptr;
  uint32_t width = 1;
};

struct RtlirModuleInst {
  std::string_view module_name;
  std::string_view inst_name;
  struct RtlirModule* resolved = nullptr;
  std::vector<RtlirPortBinding> port_bindings;
  std::vector<ResolvedAttribute> attrs;
  bool is_bound = false;
};

struct RtlirImport {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
};

struct RtlirEnumMember {
  std::string_view name;
  int64_t value = 0;
};

struct RtlirModule {
  std::string_view name;

  std::string_view library;
  bool has_param_port_list = false;
  bool is_program = false;
  std::vector<ResolvedAttribute> attrs;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;

  std::vector<RtlirPort> ports;
  std::vector<RtlirNet> nets;
  std::vector<RtlirVariable> variables;
  std::vector<RtlirContAssign> assigns;
  std::vector<RtlirAlias> aliases;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  std::vector<ModuleItem*> function_decls;
  std::vector<ModuleItem*> let_decls;
  std::vector<ModuleItem*> sequence_decls;
  std::vector<ClassDecl*> class_decls;
  std::vector<RtlirImport> imports;

  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enum_types;
};

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;

  std::unordered_map<std::string_view, uint32_t> type_widths;

  std::vector<ModuleItem*> cu_function_decls;

  std::vector<ModuleItem*> cu_let_decls;

  std::vector<PackageDecl*> packages;

  std::vector<ClassDecl*> cu_class_decls;
};

}
