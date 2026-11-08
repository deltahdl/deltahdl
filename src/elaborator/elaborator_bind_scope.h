#pragma once

#include <string_view>

namespace delta {

struct ModuleItem;
struct Expr;
struct RtlirModule;
struct RtlirModuleInst;
struct RtlirPort;
struct RtlirPortBinding;

struct PortBindScope {
  RtlirModuleInst& inst;
  const ModuleItem* item;
  RtlirModule* parent_mod;
  bool has_pull;
  bool is_ordered;
};

struct ExplicitPortBind {
  RtlirPortBinding& binding;
  const Expr* conn_expr;
  std::string_view port_name;
  const RtlirPort* child_port;
  bool is_implicit;
};

}  // namespace delta
