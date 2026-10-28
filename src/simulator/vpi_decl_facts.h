#pragma once

namespace delta {

struct ModuleDecl;
struct VpiObject;

// §37.17 and §37.41: what the declaration of a variable or of a task or
// function says of it that the model reports as properties beside its kind.
struct VpiDeclFacts {
  // §37.17 detail 24 and §37.41 detail 4: the visibility a class member was
  // declared with, vpiLocalVis or vpiProtectedVis, and 0 for one declared
  // with neither.
  int visibility = 0;
  // §37.17 (printed page 1025) with §6.20.6: whether a variable was declared
  // const, which vpi_get(vpiConstantVariable) reports.
  bool constant_variable = false;
  // §37.17 detail 8: the expression a variable's declaration initializes it
  // with, reached through vpiExpr; null where it writes none.
  VpiObject* init_expr = nullptr;
  // §25.9 with §37.48: the declaration of the interface a virtual interface
  // var's declaration refers to an instance of, whose clocking blocks the var
  // names whether or not the design instantiates the interface; null for any
  // other variable.
  const ModuleDecl* vif_interface = nullptr;
  // §6.11.2: whether a task's or function's variable (§37.12), which the run
  // keeps no storage of its own for, was declared of a 2-state type: a packed
  // structure or union with no 4-state member (§7.2.1, §7.3.1), an
  // enumeration of a 2-state base (§6.19), or a 2-state integer type.
  bool two_state = false;
};

}  // namespace delta
