#pragma once

#include <string_view>

namespace delta {

struct ModuleItem;
struct Expr;
struct RtlirModule;
struct RtlirModuleInst;
struct RtlirPort;
struct RtlirPortBinding;

// §23.3.3 per-instance binding scope shared by the BindPorts helpers.
struct PortBindScope {
  RtlirModuleInst& inst;
  const ModuleItem* item;
  RtlirModule* parent_mod;
  bool has_pull;
  bool is_ordered;
};

// Mutable per-connection state threaded through the BindExplicitPort helpers.
struct ExplicitPortBind {
  RtlirPortBinding& binding;
  const Expr* conn_expr;
  std::string_view port_name;
  const RtlirPort* child_port;  // nullptr when no port matches
  bool is_implicit;
};

}  // namespace delta
