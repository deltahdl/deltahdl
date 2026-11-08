#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ConstraintDistribution : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(ConstraintDistribution, ConstraintItemIterationReturnsItemsInOrder) {
  VpiObject ordering;
  ordering.type = vpiConstraintOrdering;
  VpiObject not_item;
  not_item.type = vpiAttribute;
  VpiObject implication;
  implication.type = vpiImplication;
  VpiObject expr;
  expr.type = vpiOperation;
  VpiObject var;
  var.type = vpiIntVar;

  VpiObject constraint;
  constraint.type = vpiConstraint;
  constraint.children = {&ordering, &not_item, &implication, &expr, &var};

  vpiHandle it = vpi_iterate(vpiConstraintItem, VpiHandleOf(&constraint));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 4u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &ordering);
  EXPECT_EQ(VpiObjectOf(seen[1]), &implication);
  EXPECT_EQ(VpiObjectOf(seen[2]), &expr);
  EXPECT_EQ(VpiObjectOf(seen[3]), &var);
}

TEST_F(ConstraintDistribution, ConstraintIterationReturnsDeclarationOrder) {
  VpiObject c0;
  c0.type = vpiConstraint;
  VpiObject other;
  other.type = vpiReg;
  VpiObject c1;
  c1.type = vpiConstraint;
  VpiObject c2;
  c2.type = vpiConstraint;

  VpiObject class_obj;
  class_obj.type = vpiClassDefn;
  class_obj.children = {&c0, &other, &c1, &c2};

  vpiHandle it = vpi_iterate(vpiConstraint, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &c0);
  EXPECT_EQ(VpiObjectOf(seen[1]), &c1);
  EXPECT_EQ(VpiObjectOf(seen[2]), &c2);
}

TEST_F(ConstraintDistribution, ExternConstraintKeepsPrototypePosition) {
  VpiObject c0;
  c0.type = vpiConstraint;
  VpiObject c_extern;
  c_extern.type = vpiConstraint;
  c_extern.access_type = vpiExternAcc;
  VpiObject c2;
  c2.type = vpiConstraint;

  VpiObject class_obj;
  class_obj.type = vpiClassDefn;
  class_obj.children = {&c0, &c_extern, &c2};

  vpiHandle it = vpi_iterate(vpiConstraint, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &c0);
  EXPECT_EQ(VpiObjectOf(seen[1]), &c_extern);
  EXPECT_EQ(VpiObjectOf(seen[2]), &c2);
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&c_extern)), vpiExternAcc);
}

TEST_F(ConstraintDistribution, AccessTypeIsExternAccOrZero) {
  VpiObject extern_constraint;
  extern_constraint.type = vpiConstraint;
  extern_constraint.access_type = vpiExternAcc;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&extern_constraint)),
            vpiExternAcc);

  VpiObject local_constraint;
  local_constraint.type = vpiConstraint;
  local_constraint.access_type = 0;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&local_constraint)), 0);

  VpiObject odd_constraint;
  odd_constraint.type = vpiConstraint;
  odd_constraint.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&odd_constraint)), 0);

  VpiObject non_constraint;
  non_constraint.type = vpiFunction;
  non_constraint.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&non_constraint)), 99);
}

TEST_F(ConstraintDistribution, AutomaticReflectsKeywordNotLifetime) {
  VpiObject static_constraint;
  static_constraint.type = vpiConstraint;
  static_constraint.automatic = false;
  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&static_constraint)), 0);

  VpiObject automatic_constraint;
  automatic_constraint.type = vpiConstraint;
  automatic_constraint.automatic = true;
  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&automatic_constraint)), 1);
}

TEST_F(ConstraintDistribution, ScalarPropertiesAreReported) {
  VpiObject constraint;
  constraint.type = vpiConstraint;
  constraint.is_virtual = true;
  constraint.constraint_enabled = true;
  EXPECT_EQ(vpi_get(vpiVirtual, VpiHandleOf(&constraint)), 1);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, VpiHandleOf(&constraint)), 1);

  VpiObject plain_constraint;
  plain_constraint.type = vpiConstraint;
  EXPECT_EQ(vpi_get(vpiVirtual, VpiHandleOf(&plain_constraint)), 0);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, VpiHandleOf(&plain_constraint)), 0);

  VpiObject dist_item;
  dist_item.type = vpiDistItem;
  dist_item.dist_type = vpiDivDist;
  EXPECT_EQ(vpi_get(vpiDistType, VpiHandleOf(&dist_item)), vpiDivDist);
}

class ConstraintsOfARun : public VpiDesignRun {
 protected:
  static std::vector<std::string> ConstraintNames(vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(vpiConstraint, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }
};

TEST_F(ConstraintsOfARun, AClassDefnIteratesItsConstraints) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c { x > 0; }\n"
      "    extern constraint e;\n"
      "    static constraint d { x < 9; }\n"
      "  endclass\n"
      "  constraint C::e { x != 3; }\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(ConstraintNames(defn), (std::vector<std::string>{"c", "e", "d"}));
  vpiHandle c = Named(vpiConstraint, defn, "c");
  vpiHandle e = Named(vpiConstraint, defn, "e");
  vpiHandle d = Named(vpiConstraint, defn, "d");
  ASSERT_NE(c, nullptr);
  ASSERT_NE(e, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, c), "top.C::c");
  EXPECT_EQ(vpi_get(vpiAutomatic, c), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, d), 0);
  EXPECT_EQ(vpi_get(vpiAccessType, c), 0);
  EXPECT_EQ(vpi_get(vpiAccessType, e), vpiExternAcc);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, c), 1);
}

TEST_F(ConstraintsOfARun, AClassObjIteratesItsConstraints) {
  Run("module top;\n"
      "  class B; rand int x; constraint b { x < 9; } endclass\n"
      "  class C extends B;\n"
      "    constraint c { x > 0; }\n"
      "    static constraint s { x != 3; }\n"
      "  endclass\n"
      "  C h = new;\n"
      "  initial begin : p h.c.constraint_mode(0); h.s.constraint_mode(0); "
      "end\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(ConstraintNames(obj), (std::vector<std::string>{"b", "c", "s"}));
  vpiHandle b = Named(vpiConstraint, obj, "b");
  vpiHandle c = Named(vpiConstraint, obj, "c");
  vpiHandle s = Named(vpiConstraint, obj, "s");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, c)), VpiObjectOf(obj));
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, b), 1);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, c), 0);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, s), 0);
  const std::vector<vpiHandle> kCalls =
      ObjectsOf(vpiMethodFuncCall, By("top.p"));
  ASSERT_EQ(kCalls.size(), 2U);
  vpiHandle prefix = vpi_handle(vpiPrefix, kCalls.front());
  ASSERT_NE(prefix, nullptr);
  EXPECT_EQ(vpi_get(vpiType, prefix), vpiConstraint);
}

TEST_F(ConstraintsOfARun, OnlyAClassObjsConstraintReachesAParent) {
  Run("module top; class C; rand int x; constraint c { x > 0; } endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiConstraint, Named(vpiClassDefn, By("top"), "C"), "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_handle(vpiParent, c), nullptr);
  VpiObject loose;
  loose.type = vpiConstraint;
  EXPECT_EQ(vpi_handle(vpiParent, VpiHandleOf(&loose)), nullptr);
}

TEST_F(ConstraintsOfARun, AnExternConstraintHoldsItsBlocksItems) {
  Run("module top;\n"
      "  class C; rand int x; extern constraint e; endclass\n"
      "  constraint C::e { x != 3; x < 9; }\n"
      "endmodule\n");
  vpiHandle e = Named(vpiConstraint, Named(vpiClassDefn, By("top"), "C"), "e");
  ASSERT_NE(e, nullptr);
  const std::vector<vpiHandle> kItems = ObjectsOf(vpiConstraintItem, e);
  ASSERT_EQ(kItems.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kItems[0]), vpiNeqOp);
  EXPECT_EQ(vpi_get(vpiOpType, kItems[1]), vpiLtOp);
}

TEST_F(ConstraintsOfARun, APureConstraintIsVirtual) {
  Run("module top;\n"
      "  virtual class A; rand int x; pure constraint p; endclass\n"
      "  class C extends A; constraint p { x > 0; } endclass\n"
      "endmodule\n");
  vpiHandle pure =
      Named(vpiConstraint, Named(vpiClassDefn, By("top"), "A"), "p");
  vpiHandle fulfilling =
      Named(vpiConstraint, Named(vpiClassDefn, By("top"), "C"), "p");
  ASSERT_NE(pure, nullptr);
  ASSERT_NE(fulfilling, nullptr);
  EXPECT_EQ(vpi_get(vpiVirtual, pure), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, fulfilling), 0);
  EXPECT_EQ(vpi_get(vpiAccessType, pure), 0);
}

}  // namespace
}  // namespace delta
