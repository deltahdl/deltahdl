#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

// Forward declarations from parser/ast.h
struct Expr;
struct Stmt;
enum class Direction : uint8_t;
enum class DataTypeKind : uint8_t;
enum class AlwaysKind : uint8_t;

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

enum class ProcessKind : uint8_t {
  kInitial,
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
};

// --- Variable ---

struct RtlirVariable {
  std::string_view name;
  uint32_t width = 1;
  bool is_4state = true;
};

// --- Continuous assignment ---

struct RtlirContAssign {
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
};

// --- Process block ---

struct RtlirProcess {
  ProcessKind kind = ProcessKind::kInitial;
  Stmt* body = nullptr;
};

// --- Parameter declaration ---

struct RtlirParamDecl {
  std::string_view name;
  Expr* default_value = nullptr;
  int64_t resolved_value = 0;
  bool is_resolved = false;
};

// --- Module instance (child) ---

struct RtlirModuleInst {
  std::string_view module_name;
  std::string_view inst_name;
  struct RtlirModule* resolved = nullptr;
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
};

// --- Design (top-level container) ---

struct RtlirDesign {
  std::vector<RtlirModule*> top_modules;
  std::unordered_map<std::string_view, RtlirModule*> all_modules;
};

}  // namespace delta
