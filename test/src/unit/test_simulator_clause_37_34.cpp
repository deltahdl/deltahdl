#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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
// it groups - the constraint orderings and constraint expressions - in the
// order they occur, and nothing else. A child that is neither (here an ordinary
// operation expression) is excluded, showing the grouping matches the
// constraint-item kinds rather than every expression.
TEST_F(ConstraintDistribution, ConstraintItemIterationReturnsItemsInOrder) {
  VpiObject ordering;
  ordering.type = vpiConstraintOrdering;  // a solve-before/after ordering
  VpiObject not_item;
  not_item.type = vpiOperation;  // an expression that is not a constraint item
  VpiObject expr;
  expr.type = vpiConstraintExpr;  // a constraint expression

  VpiObject constraint;
  constraint.type = vpiConstraint;
  constraint.children = {&ordering, &not_item, &expr};

  vpiHandle it = vpi_iterate(vpiConstraintItem, &constraint);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 2u);     // the non-item child is excluded
  EXPECT_EQ(seen[0], &ordering);  // occurrence order is preserved
  EXPECT_EQ(seen[1], &expr);
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

  vpiHandle it = vpi_iterate(vpiConstraint, &class_obj);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);  // the non-constraint child is excluded
  EXPECT_EQ(seen[0], &c0);     // declaration order is preserved
  EXPECT_EQ(seen[1], &c1);
  EXPECT_EQ(seen[2], &c2);
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
  EXPECT_EQ(vpi_get(vpiAccessType, &extern_constraint), vpiExternAcc);

  VpiObject local_constraint;
  local_constraint.type = vpiConstraint;
  local_constraint.access_type = 0;
  EXPECT_EQ(vpi_get(vpiAccessType, &local_constraint), 0);

  // Any other stored value collapses to zero for a constraint.
  VpiObject odd_constraint;
  odd_constraint.type = vpiConstraint;
  odd_constraint.access_type = 99;  // not vpiExternAcc
  EXPECT_EQ(vpi_get(vpiAccessType, &odd_constraint), 0);

  // The clamp is scoped to constraints: a non-constraint passes its value
  // through.
  VpiObject non_constraint;
  non_constraint.type = vpiReg;
  non_constraint.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, &non_constraint), 99);
}

// D1: for a constraint, vpiAutomatic reflects the keyword written on the
// declaration rather than a storage lifetime. A constraint declared without the
// automatic keyword (static) reports zero; one declared with it reports one.
TEST_F(ConstraintDistribution, AutomaticReflectsKeywordNotLifetime) {
  VpiObject static_constraint;
  static_constraint.type = vpiConstraint;
  static_constraint.automatic = false;  // declared static
  EXPECT_EQ(vpi_get(vpiAutomatic, &static_constraint), 0);

  VpiObject automatic_constraint;
  automatic_constraint.type = vpiConstraint;
  automatic_constraint.automatic = true;  // declared with the automatic keyword
  EXPECT_EQ(vpi_get(vpiAutomatic, &automatic_constraint), 1);
}

// The diagram's int/bool constraint and dist-item properties: vpiVirtual and
// vpiIsConstraintEnabled are field-backed Booleans on a constraint, and
// vpiDistType is the int distribution kind a dist item carries.
TEST_F(ConstraintDistribution, ScalarPropertiesAreReported) {
  VpiObject constraint;
  constraint.type = vpiConstraint;
  constraint.is_virtual = true;
  constraint.constraint_enabled = true;
  EXPECT_EQ(vpi_get(vpiVirtual, &constraint), 1);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, &constraint), 1);

  VpiObject plain_constraint;
  plain_constraint.type = vpiConstraint;
  EXPECT_EQ(vpi_get(vpiVirtual, &plain_constraint), 0);
  EXPECT_EQ(vpi_get(vpiIsConstraintEnabled, &plain_constraint), 0);

  VpiObject dist_item;
  dist_item.type = vpiDistItem;
  dist_item.dist_type = vpiDivDist;
  EXPECT_EQ(vpi_get(vpiDistType, &dist_item), vpiDivDist);
}

}  // namespace
}  // namespace delta
