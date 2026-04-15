#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

// --- Resolved attribute (§5.12 / A.9.1) ---

struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;  // Constant-evaluated integer value.
  std::string_view string_value;          // String literal value (if any).
};

// --- RTLIR node classification ---

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

// --- Process kind (elaborated from AST always kinds) ---

enum class RtlirProcessKind : uint8_t {
  kInitial,
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
  kFinal,
};

// --- Port ---

struct RtlirPort {
  std::string_view name;
  Direction direction;
  DataTypeKind type_kind;
  uint32_t width = 1;
  bool is_signed = false;
  bool is_var = false;
  Expr* default_value = nullptr;
  std::vector<ResolvedAttribute> attrs;
};

// --- Net ---

struct RtlirNet {
  std::string_view name;
  NetType net_type = NetType::kWire;
  uint32_t width = 1;
  std::vector<uint32_t> driver_indices;
  // §6.6.4: Trireg charge strength and decay time.
  Strength charge_strength = Strength::kMedium;
  uint32_t trireg_capacitance = 0;  // §E.3: 0-250 numeric capacitance.
  uint64_t decay_ticks = 0;
  // §6.9.2: Vector net accessibility.
  bool is_vectored = false;
  bool is_scalared = false;
  // §6.6.7: User-defined nettype.
  bool is_user_nettype = false;
  std::string_view resolve_func;
  std::vector<ResolvedAttribute> attrs;
};

// --- Variable ---

struct RtlirVariable {
  std::string_view name;
  uint32_t width = 1;
  bool is_4state = true;
  bool is_event = false;
  bool is_string = false;
  bool is_real = false;
  bool is_signed = false;
  bool is_chandle = false;          // §6.14: chandle type (defaults to null).
  const Expr* init_expr = nullptr;  // Module-level variable initializer.
  const DataType* dtype = nullptr;  // Full type for struct/union layout.
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;  // §10.9.1: element type for type-key matching.
  uint32_t unpacked_size = 0;       // §7.4: unpacked array element count.
  uint32_t unpacked_lo = 0;         // §7.4: unpacked array low index.
  bool is_descending = false;       // §7.4: true for [hi:lo] range.
  bool is_dynamic = false;          // §7.5: dynamic array declared with [].
  bool is_queue = false;            // §7.10: queue declared with [$].
  int32_t queue_max_size = -1;      // §7.10: max queue size (-1=unbounded).
  bool is_assoc = false;            // §7.8: associative array.
  bool is_string_index = false;     // §7.8: true if index type is string.
  bool is_wildcard_index = false;   // §7.8.1: true if index type is [*].
  bool is_class_index = false;      // §7.8.3: true if index type is a class.
  uint32_t assoc_index_width = 32;  // §7.9.8: width of assoc index type.
  std::string_view assoc_index_class_name;  // §7.8.3: class index type name.
  std::string_view class_type_name;  // §8: class type name for class variables.
  std::string_view enum_type_name;   // §6.19: enum type name for $cast.
  std::vector<ResolvedAttribute> attrs;
};

// --- Continuous assignment ---

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  uint32_t width = 0;
  uint8_t drive_strength0 = 0;  // §10.3.4: 0=none,1=highz,...,5=supply
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;        // §10.3.3: rise delay (or single delay)
  Expr* delay_fall = nullptr;   // §10.3.3: fall delay
  Expr* delay_decay = nullptr;  // §10.3.3: turn-off delay
  std::vector<ResolvedAttribute> attrs;
};

// --- Net alias (§10.11) ---

struct RtlirAlias {
  std::vector<Expr*> nets;
};

// --- Process block ---

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  bool is_star_sensitivity = false;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
  std::vector<ResolvedAttribute> attrs;
};

// --- Parameter declaration ---

struct RtlirParamDecl {
  std::string_view name;
  Expr* default_value = nullptr;
  int64_t resolved_value = 0;
  bool is_resolved = false;
  bool is_localparam = false;  // §A.2.1.1: localparam vs parameter.
  bool from_override = false;  // True when set via instance #(...) override.
  bool is_unbounded = false;   // §6.20.7: parameter assigned $.
  bool is_type_param = false;  // §6.20.3: type parameter.
};

// --- Port binding (for module instances) ---

struct RtlirPortBinding {
  std::string_view port_name;
  Direction direction;
  Expr* connection = nullptr;
  uint32_t width = 1;
};

// --- Module instance (child) ---

struct RtlirModuleInst {
  std::string_view module_name;
  std::string_view inst_name;
  struct RtlirModule* resolved = nullptr;
  std::vector<RtlirPortBinding> port_bindings;
  std::vector<ResolvedAttribute> attrs;
};

// --- Module ---

// §6.19: Enum member info for lowerer → SimContext registration.
struct RtlirEnumMember {
  std::string_view name;
  int64_t value = 0;
};

struct RtlirModule {
  std::string_view name;
  bool has_param_port_list = false;  // §6.20.1: #(...) was present.
  std::vector<ResolvedAttribute> attrs;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;  // §E.4-E.7

  std::vector<RtlirPort> ports;
  std::vector<RtlirNet> nets;
  std::vector<RtlirVariable> variables;
  std::vector<RtlirContAssign> assigns;
  std::vector<RtlirAlias> aliases;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  std::vector<ModuleItem*> function_decls;
  std::vector<ModuleItem*> let_decls;  // §A.2.12: let declarations in module.
  std::vector<ModuleItem*> sequence_decls;
  std::vector<ClassDecl*> class_decls;  // §8: class declarations in module.
  // §6.19/§6.24.2: enum type → members, for $cast and enum methods.
  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enum_types;
};

// --- Design (top-level container) ---

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;
  // §20.6.2: type name → bit width, populated from typedefs for $bits(type).
  std::unordered_map<std::string_view, uint32_t> type_widths;
  // §3.12.1: CU-scope function/task declarations visible to all modules.
  std::vector<ModuleItem*> cu_function_decls;
  // §11.12: CU-scope let declarations visible to all modules.
  std::vector<ModuleItem*> cu_let_decls;
};

}  // namespace delta
