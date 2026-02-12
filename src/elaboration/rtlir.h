#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

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
};

// --- Net ---

struct RtlirNet {
  std::string_view name;
  NetType net_type = NetType::kWire;
  uint32_t width = 1;
  std::vector<uint32_t> driver_indices;
  // §6.6.4: Trireg charge strength and decay time.
  Strength charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
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
  const Expr* init_expr = nullptr;   // Module-level variable initializer.
  const DataType* dtype = nullptr;   // Full type for struct/union layout.
  uint32_t unpacked_size = 0;        // §7.4: unpacked array element count.
  uint32_t unpacked_lo = 0;          // §7.4: unpacked array low index.
  bool is_descending = false;        // §7.4: true for [hi:lo] range.
  bool is_queue = false;             // §7.10: queue declared with [$].
  int32_t queue_max_size = -1;       // §7.10: max queue size (-1=unbounded).
  bool is_assoc = false;             // §7.8: associative array.
  bool is_string_index = false;      // §7.8: true if index type is string.
  std::string_view class_type_name;  // §8: class type name for class variables.
};

// --- Continuous assignment ---

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  uint32_t width = 0;
  uint8_t drive_strength0 = 0;  // §10.3.4: 0=none,1=highz,...,5=supply
  uint8_t drive_strength1 = 0;
};

// --- Process block ---

struct RtlirProcess {
  RtlirProcessKind kind = RtlirProcessKind::kInitial;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;
};

// --- Parameter declaration ---

struct RtlirParamDecl {
  std::string_view name;
  Expr* default_value = nullptr;
  int64_t resolved_value = 0;
  bool is_resolved = false;
  bool from_override = false;  // True when set via instance #(...) override.
  bool is_unbounded = false;   // §6.20.7: parameter assigned $.
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
};

// --- Module ---

struct RtlirModule {
  std::string_view name;

  std::vector<RtlirPort> ports;
  std::vector<RtlirNet> nets;
  std::vector<RtlirVariable> variables;
  std::vector<RtlirContAssign> assigns;
  std::vector<RtlirProcess> processes;
  std::vector<RtlirModuleInst> children;
  std::vector<RtlirParamDecl> params;
  std::vector<ModuleItem*> function_decls;
  std::vector<ClassDecl*> class_decls;  // §8: class declarations in module.
};

// --- Design (top-level container) ---

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;
  // §20.6.2: type name → bit width, populated from typedefs for $bits(type).
  std::unordered_map<std::string_view, uint32_t> type_widths;
};

}  // namespace delta
