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

// §37.34 Constraint, constraint ordering, distribution: the VPI object model
// for a constraint, its constraint items (constraint orderings and constraint
// expressions), and the distribution / dist-item objects. The diagram's bare
// relation arrows (vpiParent to the class obj, the constraint-ordering
// vpiSolveBefore/vpiSolveAfter edges to exprs, the dist-item vpiValueRange/
// vpiWeight edges, the distribution<->dist-item link) carry no clause-specific
// rule and are served by the generic object-model and §38 traversal routines.
// This clause's own rules are the numbered Details, and the tests below observe
// the production code that applies them:
//   D1 - for a constraint, vpiAutomatic reflects the declaration keyword (not a
//        lifetime); zero means it was declared static (the kVpiAutomatic
//        dispatch, observed on a constraint object).
//   D2 - the memory-allocation property is owned by §37.3.7 (delegated).
//   D3 - a constraint's vpiAccessType is vpiExternAcc or zero, never a third
//        value (the vpiAccessType dispatch with its constraint clamp).
//   D4 - the vpiConstraint iteration returns constraints in declaration order
//        (the ordered child walk of Iterate).
//   D5 - the vpiConstraintItem iteration returns the constraint items in the
//        order they occur (the VpiIsConstraintItemType grouping in Iterate).
// The diagram also annotates the int/bool constraint and dist-item properties
// (vpiVirtual, vpiIsConstraintEnabled, vpiDistType); these are field-backed
// getters observed at the end.

// The fixture installs a context so the public vpi_get/vpi_iterate/vpi_scan
// entry points run their real dispatch.
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

// D5: a constraint's vpiConstraintItem iteration collects the constraint items
// it groups - the constraint orderings and the kinds §37.38's constraint expr
// class groups, an expression such as an operation among them - in the order
// they occur, and nothing else. An attribute child is no constraint item and is
// excluded, showing the grouping matches the constraint-item kinds rather than
// every child (#5841).
TEST_F(ConstraintDistribution, ConstraintItemIterationReturnsItemsInOrder) {
  VpiObject ordering;
  ordering.type = vpiConstraintOrdering;  // a solve-before/after ordering
  VpiObject not_item;
  not_item.type = vpiAttribute;  // an attribute, no constraint item
  VpiObject implication;
  implication.type = vpiImplication;  // a constraint expression
  VpiObject expr;
  expr.type = vpiOperation;  // an expression, a constraint expression too
  VpiObject var;
  var.type = vpiIntVar;  // a name standing alone as a constraint expression

  VpiObject constraint;
  constraint.type = vpiConstraint;
  constraint.children = {&ordering, &not_item, &implication, &expr, &var};

  vpiHandle it = vpi_iterate(vpiConstraintItem, VpiHandleOf(&constraint));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 4u);                  // the non-item child is excluded
  EXPECT_EQ(VpiObjectOf(seen[0]), &ordering);  // occurrence order is preserved
  EXPECT_EQ(VpiObjectOf(seen[1]), &implication);
  EXPECT_EQ(VpiObjectOf(seen[2]), &expr);
  EXPECT_EQ(VpiObjectOf(seen[3]), &var);
}

// D4: the vpiConstraint iteration returns a class's constraints in syntactic
// declaration order. The constraints are stored as children in that order, and
// a non-constraint child is filtered out, so the iteration hands them back in
// order.
TEST_F(ConstraintDistribution, ConstraintIterationReturnsDeclarationOrder) {
  VpiObject c0;
  c0.type = vpiConstraint;
  VpiObject other;
  other.type = vpiReg;  // a class member that is not a constraint
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

  ASSERT_EQ(seen.size(), 3u);            // the non-constraint child is excluded
  EXPECT_EQ(VpiObjectOf(seen[0]), &c0);  // declaration order is preserved
  EXPECT_EQ(VpiObjectOf(seen[1]), &c1);
  EXPECT_EQ(VpiObjectOf(seen[2]), &c2);
}

// D4 (second sentence): the position of a constraint declared extern is
// determined by its prototype's position, so the vpiConstraint iteration must
// hand back an extern constraint in its declaration-order slot rather than
// reorder or drop it. Here the extern constraint (reporting vpiExternAcc, the
// input form that distinguishes it from the ordinary declarations around it)
// sits between two local constraints and comes back in that middle position.
TEST_F(ConstraintDistribution, ExternConstraintKeepsPrototypePosition) {
  VpiObject c0;
  c0.type = vpiConstraint;  // an ordinary in-class constraint
  VpiObject c_extern;
  c_extern.type = vpiConstraint;
  c_extern.access_type = vpiExternAcc;  // declared extern; positioned by proto
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
  EXPECT_EQ(VpiObjectOf(seen[1]),
            &c_extern);  // the extern constraint holds its slot
  EXPECT_EQ(VpiObjectOf(seen[2]), &c2);
  // Its extern-ness is what the ordering had to preserve past, confirmed here.
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&c_extern)), vpiExternAcc);
}

// D3: a constraint's vpiAccessType reports vpiExternAcc when it is declared
// outside its enclosing class declaration and zero otherwise - never a third
// value. A stored value that is neither collapses to zero. The clamp is
// specific to constraints, so another object kind reports its stored access
// type as-is.
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

  // Any other stored value collapses to zero for a constraint.
  VpiObject odd_constraint;
  odd_constraint.type = vpiConstraint;
  odd_constraint.access_type = 99;  // not vpiExternAcc
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&odd_constraint)), 0);

  // The clamp is scoped to constraints: another object the property is drawn
  // on keeps its own rule. §37.41 draws it on the task func enclosure, where a
  // function reports the access it was declared with.
  VpiObject non_constraint;
  non_constraint.type = vpiFunction;
  non_constraint.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&non_constraint)), 99);
}

// D1: for a constraint, vpiAutomatic reflects the keyword written on the
// declaration rather than a storage lifetime. A constraint declared without the
// automatic keyword (static) reports zero; one declared with it reports one.
TEST_F(ConstraintDistribution, AutomaticReflectsKeywordNotLifetime) {
  VpiObject static_constraint;
  static_constraint.type = vpiConstraint;
  static_constraint.automatic = false;  // declared static
  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&static_constraint)), 0);

  VpiObject automatic_constraint;
  automatic_constraint.type = vpiConstraint;
  automatic_constraint.automatic = true;  // declared with the automatic keyword
  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&automatic_constraint)), 1);
}

// The diagram's int/bool constraint and dist-item properties: vpiVirtual and
// vpiIsConstraintEnabled are field-backed Booleans on a constraint, and
// vpiDistType is the int distribution kind a dist item carries.
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

// A design run with a PLI application registered, whose class defns' and
// class objects' constraints are read back from the model the run built.
class ConstraintsOfARun : public VpiDesignRun {
 protected:
  // The names of the constraints `ref` iterates, in the iteration's order.
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

// §37.31 with §37.34: a class defn iterates a constraint per constraint block
// the class declares, in declaration order, an extern one in its prototype's
// place (D4). Each is named after its block and full-named through the class,
// reports vpiAutomatic 0 only where it was declared
// static (D1, §18.5.10) and vpiExternAcc only where a prototype declares it
// (D3, §18.5.1), and is enabled, as every constraint is at first (§18.9)
// (#5839).
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

// §37.33 with §37.34: a class obj iterates a constraint per constraint block
// of the class it was created with and the classes that class extends, the
// base's first. Each reaches the class obj through vpiParent, and reports as
// enabled what constraint_mode() last set on the object (§18.9), a static
// block's state being the class's (§18.5.10). A call of constraint_mode
// applied to a block is applied to that block's constraint of the object the
// handle references (§37.42 detail 2) (#5838).
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
  vpiHandle call = Named(vpiMethodFuncCall, By("top.p"), "constraint_mode");
  ASSERT_NE(call, nullptr);
  vpiHandle prefix = vpi_handle(vpiPrefix, call);
  ASSERT_NE(prefix, nullptr);
  EXPECT_EQ(vpi_get(vpiType, prefix), vpiConstraint);
}

// §37.34: the figure draws a constraint's vpiParent to the class obj holding
// it and from nowhere else, so a class defn's constraint, and one held by
// nothing, reach none.
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

}  // namespace
}  // namespace delta
