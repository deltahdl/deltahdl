#pragma once

namespace delta {

struct ModuleDecl;
struct VpiObject;

struct VpiDeclFacts {
  int visibility = 0;
  bool constant_variable = false;
  VpiObject* init_expr = nullptr;
  const ModuleDecl* vif_interface = nullptr;
  bool two_state = false;
};

}  // namespace delta
