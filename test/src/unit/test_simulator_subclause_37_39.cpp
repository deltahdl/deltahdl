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

// -----------------------------------------------------------------------------
// The properties and the path-term relations §37.39 draws. A module path
// reports which kind of path it is, the polarity of the path and of its data
// path, and whether it carries an ifnone condition; a path term reports the
// edge it is sensitive to beside its direction; and three relations reach the
// terms. None of them was served: the property switch named none of the four,
// and each of the three relations is a tag no object's type is, so the generic
// traversal reached the terms of no module path in any design.
// -----------------------------------------------------------------------------

// Diagram (mod path properties): a module path reports its path type, its two
// polarities and its ifnone flag.
TEST_F(ModulePathModel, AModulePathReportsItsOwnProperties) {
  VpiObject path;
  path.type = vpiModPath;
  path.path_type = vpiPathParallel;
  path.polarity = vpiPositive;
  path.data_polarity = vpiNegative;
  path.mod_path_has_if_none = true;

  EXPECT_EQ(vpi_get(vpiPathType, &path), vpiPathParallel);
  EXPECT_EQ(vpi_get(vpiPolarity, &path), vpiPositive);
  EXPECT_EQ(vpi_get(vpiDataPolarity, &path), vpiNegative);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, &path), 1);

  // A full-connection path written without an ifnone reports the other kind and
  // a false flag, so neither value is whatever the field happened to hold.
  VpiObject full;
  full.type = vpiModPath;
  full.path_type = vpiPathFull;
  EXPECT_EQ(vpi_get(vpiPathType, &full), vpiPathFull);
  EXPECT_EQ(vpi_get(vpiModPathHasIfNone, &full), 0);
}

// Diagram (path term properties): a path term reports the edge it is sensitive
// to, alongside the direction the same object carries.
TEST_F(ModulePathModel, APathTermReportsItsEdgeAndDirection) {
  VpiObject term;
  term.type = vpiPathTerm;
  term.direction = kVpiInput;
  term.edge = vpiEdge01;

  EXPECT_EQ(vpi_get(vpiEdge, &term), vpiEdge01);
  EXPECT_EQ(vpi_get(kVpiDirection, &term), kVpiInput);
}

// Diagram (mod path -> path term, three relations): the output terms come back
// from vpiModPathOut, the plain input terms from vpiModPathIn, and the data
// source of an edge-sensitive path from vpiModDataPathIn. The three sets are
// disjoint, so a term reached by one is reached by neither of the others.
TEST_F(ModulePathModel, TheThreeTermRelationsReachTheirOwnTerms) {
  VpiObject in_term;
  in_term.type = vpiPathTerm;
  in_term.direction = kVpiInput;
  VpiObject data_term;
  data_term.type = vpiPathTerm;
  data_term.direction = kVpiInput;
  data_term.data_path_term = true;
  VpiObject out_term;
  out_term.type = vpiPathTerm;
  out_term.direction = kVpiOutput;
  VpiObject not_a_term;
  not_a_term.type = vpiConstant;

  VpiObject path;
  path.type = vpiModPath;
  path.children = {&in_term, &data_term, &out_term, &not_a_term};

  vpiHandle ins = vpi_iterate(vpiModPathIn, &path);
  ASSERT_NE(ins, nullptr);
  EXPECT_EQ(vpi_scan(ins), &in_term);
  EXPECT_EQ(vpi_scan(ins), nullptr);

  vpiHandle datas = vpi_iterate(vpiModDataPathIn, &path);
  ASSERT_NE(datas, nullptr);
  EXPECT_EQ(vpi_scan(datas), &data_term);
  EXPECT_EQ(vpi_scan(datas), nullptr);

  vpiHandle outs = vpi_iterate(vpiModPathOut, &path);
  ASSERT_NE(outs, nullptr);
  EXPECT_EQ(vpi_scan(outs), &out_term);
  EXPECT_EQ(vpi_scan(outs), nullptr);
}

// Diagram: a path with no term of a given role reaches none through that
// relation, which §38.23 reports as no iterator.
TEST_F(ModulePathModel, ARelationWithNoTermOfItsRoleReachesNone) {
  VpiObject out_term;
  out_term.type = vpiPathTerm;
  out_term.direction = kVpiOutput;

  VpiObject path;
  path.type = vpiModPath;
  path.children = {&out_term};

  EXPECT_EQ(vpi_iterate(vpiModPathIn, &path), nullptr);
  EXPECT_EQ(vpi_iterate(vpiModDataPathIn, &path), nullptr);
  EXPECT_NE(vpi_iterate(vpiModPathOut, &path), nullptr);
}

}  // namespace
}  // namespace delta
