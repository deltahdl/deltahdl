#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.5 Module: the VPI object model for a module instance. Most of the diagram
// is structural and is walked by the generic object-model machinery, carrying
// no rule of its own here: the default/global clocking blocks
// (vpiDefaultClocking, vpiGlobalClocking), the default disable-iff
// expr/distribution (vpiDefaultDisableIff), the instance array and module array
// the module belongs to, and the one-to-many vpiInternalScope edges to the
// module's scopes, ports, interfaces, processes, cont assigns, nested modules,
// primitives, mod paths, timing checks, def params, io decls, alias statements,
// and clocking blocks are all reached through vpi_handle / vpi_iterate without
// a clause-specific rule.
//
// This clause carries its own normative content in two numbered Details and two
// module-specific diagram properties, each observed below through the public
// VPI dispatch:
//   D1 - top-level modules are reached by iterating vpiModule with a NULL
//        reference object; a module nested in another scope is excluded.
//   D2 - vpiIndex from a module reaches the index expression that locates it
//        within a module array, or NULL when the module is not an array
//        element.
//   vpiTopModule  - a module reports whether it is a top-level module.
//   vpiDefDecayTime - a module reports its default net decay time.

// The fixture installs a context so the public entry points run their real
// dispatch, and so module objects created through CreateModule are registered
// for the NULL-reference iteration.
class Module : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D2: vpiIndex from a module that is an element of a module array reaches the
// index expression that locates it within the array.
TEST_F(Module, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiModule;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(vpi_handle(vpiIndex, &member), &index_expr);
}

// D2: for a module that is not part of a module array, the vpiIndex transition
// returns NULL - even when an expr hangs off the object, the transition is
// meaningful only for an array element and must not surface some other child.
TEST_F(Module, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiModule;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, &standalone), nullptr);
}

// D1: iterating vpiModule with a NULL reference object reaches the top-level
// modules and only those. A nested module is also a vpiModule object but is
// reached through its parent scope, so it must not appear in this iteration.
TEST_F(Module, TopModulesReachedByNullReferenceIteration) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  top->top_module = true;

  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;

  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_top = false;
  bool saw_nested = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (h == top) saw_top = true;
    if (h == nested) saw_nested = true;
  }
  EXPECT_EQ(count, 1);
  EXPECT_TRUE(saw_top);
  EXPECT_FALSE(saw_nested);
}

// vpiTopModule: a module reports whether it is a top-level module through the
// Boolean property, observed via the public vpi_get dispatch.
TEST_F(Module, TopModulePropertyReportsTopLevelStatus) {
  VpiObject top;
  top.type = vpiModule;
  top.top_module = true;
  EXPECT_EQ(vpi_get(vpiTopModule, &top), 1);

  VpiObject nested;
  nested.type = vpiModule;
  nested.top_module = false;
  EXPECT_EQ(vpi_get(vpiTopModule, &nested), 0);
}

// vpiDefDecayTime: a module reports its default net decay time as an integer
// property through the public vpi_get dispatch.
TEST_F(Module, DefaultDecayTimeReported) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.def_decay_time = 5;
  EXPECT_EQ(vpi_get(vpiDefDecayTime, &mod), 5);
}

// D1 (edge): when the design contains modules but none is top-level, the
// NULL-reference vpiModule iteration has nothing to walk and reports a null
// handle rather than an iterator over the nested modules. Without the
// top-level filter this iteration would surface the nested module instead.
TEST_F(Module, NullReferenceIterationIsNullWhenNoModuleIsTopLevel) {
  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
}

// D1 (scope guard): the top-level filter applies only to the NULL-reference
// iteration. Iterating vpiModule over a parent scope still reaches the nested
// modules it contains, even though they are not top-level - they are reached
// through the parent, exactly as the object model intends.
TEST_F(Module, ModuleIterationOverParentScopeIsNotFilteredByTopLevel) {
  VpiHandle parent = vpi_ctx_.CreateModule("top", "top");
  parent->top_module = true;

  VpiHandle nested = vpi_ctx_.CreateModule("top.sub", "top.sub");
  nested->top_module = false;
  parent->children.push_back(nested);

  vpiHandle it = vpi_iterate(vpiModule, parent);
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_nested = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (h == nested) saw_nested = true;
  }
  EXPECT_EQ(count, 1);
  EXPECT_TRUE(saw_nested);
}

}  // namespace
}  // namespace delta
