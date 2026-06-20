#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.39 "Module path, path term": the only normative requirement the subclause
// text owns is detail 1 - the vpiModule relation is preserved for a mod path
// (specify-block path) but shall return NULL when that specify block lives in
// an interface instead of a module. These tests build a mod path under a module
// and under an interface and observe the production dispatch applying that
// rule.
class ModulePathModel : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // A context-owned object stamped with the kind the test wants, the same way
  // the §37.37 intermodule-path tests build their handles.
  VpiHandle MakeObject(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("mp", "mp");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §37.39 detail 1 (positive): a mod path whose specify block sits in a module
// reports that enclosing module through the preserved vpiModule relation.
TEST_F(ModulePathModel, ModuleReachedFromPathInModule) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  VpiHandle path = MakeObject(vpiModPath);
  path->parent = mod;
  mod->children.push_back(path);

  VpiHandle reached = vpi_handle(kVpiModule, path);
  EXPECT_EQ(reached, mod);
}

// §37.39 detail 1 (the shall): a mod path whose specify block sits in an
// interface returns NULL for vpiModule even though a module encloses that
// interface - the innermost enclosing instance is the interface, so there is no
// owning module to report. This also covers the bare interface-parent case,
// since the carve-out returns at the interface before reaching the module.
TEST_F(ModulePathModel, ModuleIsNullForInterfaceNestedInModule) {
  auto* outer = vpi_ctx_.CreateModule("wrap", "wrap");
  VpiHandle iface = MakeObject(vpiInterface);
  iface->parent = outer;
  outer->children.push_back(iface);

  VpiHandle path = MakeObject(vpiModPath);
  path->parent = iface;
  iface->children.push_back(path);

  EXPECT_EQ(vpi_handle(kVpiModule, path), nullptr);
}

// §37.39 detail 1 (scope guard): the NULL carve-out is specific to mod paths.
// A non-mod-path object directly under a module still reaches it through the
// generic vpiModule traversal, confirming the special case did not broaden.
TEST_F(ModulePathModel, CarveOutAppliesOnlyToModPath) {
  auto* mod = vpi_ctx_.CreateModule("host", "host");
  VpiHandle other = MakeObject(vpiNet);
  other->parent = mod;
  mod->children.push_back(other);

  EXPECT_EQ(vpi_handle(kVpiModule, other), mod);
}

// §37.39 detail 1 (edge): vpiModule walks the full ancestry of a mod path, not
// just its immediate parent. When the chain holds a non-instance scope and no
// enclosing module or interface at all, the relation reports NULL after the
// walk is exhausted rather than mistaking the intervening scope for a module.
TEST_F(ModulePathModel, ModuleIsNullWhenNoInstanceEncloses) {
  VpiHandle scope = MakeObject(vpiNamedBegin);
  VpiHandle path = MakeObject(vpiModPath);
  path->parent = scope;
  scope->children.push_back(path);

  EXPECT_EQ(vpi_handle(kVpiModule, path), nullptr);
}

}  // namespace
}  // namespace delta
