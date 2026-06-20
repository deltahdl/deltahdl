#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.38 Constraint expression: the VPI object model for a constraint
// expression - the group spanning an implication, a constraint if / if-else, a
// foreach constraint, a distribution, a bare (optionally soft) expression, and
// a soft disable. The diagram's bare relation arrows (vpiCondition to the
// condition expr, vpiElseConst to the else branch, the soft-disable expr edge,
// the foreach distribution/variables edges) carry no clause-specific rule and
// are served by the generic object-model and §38 traversal routines. This
// clause's own rules are its three numbered Details, and the tests below
// observe the production code that applies them:
//   D1 - the variable reached from a foreach constraint via vpiVariables
//        represents the array being indexed (the designated-pointer Handle
//        case).
//   D2 - the vpiLoopVars iteration returns the foreach index variables in
//        left-to-right order, with a skipped position reported as a
//        vpiOperation whose vpiOpType is vpiNullOp (the dedicated loop-var walk
//        of Iterate).
//   D3 - the vpiConstraintExpr iteration returns the body expressions of an
//        implication / if / if-else / foreach in the order they occur (the
//        dedicated body-list walk of Iterate).

// The fixture installs a context so the public vpi_handle/vpi_iterate/vpi_scan
// entry points run their real dispatch.
class ConstraintExpression : public ::testing::Test {
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

// D1: a foreach constraint's vpiVariables relation reaches the variable that
// represents the array being indexed. The array variable's own type is a
// variable kind, so it is held as a designated pointer and reached through the
// scoped Handle case rather than a generic child match.
TEST_F(ConstraintExpression, ForeachVariablesReachesIndexedArray) {
  VpiObject array;
  array.type = vpiArrayVar;  // the array the foreach iterates over

  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(vpi_handle(vpiVariables, &foreach), &array);
}

// D1: the relation is specific to a foreach constraint and reports NULL when no
// array is attached; it does not pick up a stray variable on another object
// kind. A non-foreach object with a vpiVariables-typed child is unaffected by
// the foreach case and still resolves through the generic walk.
TEST_F(ConstraintExpression, ForeachVariablesIsScopedAndNullWhenAbsent) {
  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;  // no array attached
  EXPECT_EQ(vpi_handle(vpiVariables, &foreach), nullptr);

  // The foreach Handle case does not fire for a different object kind: an
  // implication leaves vpiVariables to the generic traversal, which finds a
  // child whose own type is literally vpiVariables.
  VpiObject vars_child;
  vars_child.type = vpiVariables;
  VpiObject implication;
  implication.type = vpiImplication;
  implication.children = {&vars_child};
  EXPECT_EQ(vpi_handle(vpiVariables, &implication), &vars_child);
}

// D2: the vpiLoopVars iteration returns the foreach index variables in
// left-to-right order. A skipped index position - a null slot in the loop-var
// list - comes back as a placeholder operation whose operator is the null
// operation, so the caller still sees a value occupying that slot.
TEST_F(ConstraintExpression, LoopVarsIterationOrdersVarsWithNullOpPlaceholder) {
  VpiObject var_i;
  var_i.type = vpiIntVar;
  VpiObject var_k;
  var_k.type = vpiIntVar;

  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;
  // The middle index was skipped in the foreach header (a[i, , k]); a null slot
  // marks it.
  foreach
    .loop_vars = {&var_i, nullptr, &var_k};

  vpiHandle it = vpi_iterate(vpiLoopVars, &foreach);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);  // every position is reported, in order
  EXPECT_EQ(seen[0], &var_i);  // left-to-right order is preserved
  EXPECT_EQ(seen[2], &var_k);
  EXPECT_NE(seen[1], &var_i);  // the skipped slot is a fresh placeholder
  EXPECT_NE(seen[1], &var_k);
  EXPECT_EQ(vpi_get(vpiType, seen[1]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, seen[1]), vpiNullOp);
}

// D2: a foreach constraint with no skipped indices returns exactly its index
// variables, and a foreach with no index variables at all yields a null
// iterator - there is nothing to walk.
TEST_F(ConstraintExpression, LoopVarsIterationWithoutSkipsAndWhenEmpty) {
  VpiObject var_i;
  var_i.type = vpiIntVar;

  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;
  foreach
    .loop_vars = {&var_i};

  vpiHandle it = vpi_iterate(vpiLoopVars, &foreach);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &var_i);
  EXPECT_EQ(vpi_scan(it), nullptr);

  VpiObject empty_foreach;
  empty_foreach.type = vpiConstrForEach;  // no loop vars
  EXPECT_EQ(vpi_iterate(vpiLoopVars, &empty_foreach), nullptr);
}

// D2: every skipped index position is represented independently. With two
// skipped slots the iteration yields a distinct null-op placeholder for each,
// not a single shared one, so each skipped position is reported on its own.
TEST_F(ConstraintExpression, LoopVarsIterationRepresentsEachSkipIndependently) {
  VpiObject var_j;
  var_j.type = vpiIntVar;

  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;
  // The first and last indices were skipped (a[ , j, ]).
  foreach
    .loop_vars = {nullptr, &var_j, nullptr};

  vpiHandle it = vpi_iterate(vpiLoopVars, &foreach);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(seen[1], &var_j);   // the present index keeps its slot
  EXPECT_NE(seen[0], seen[2]);  // each skip is its own placeholder
  EXPECT_EQ(vpi_get(vpiType, seen[0]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, seen[0]), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiType, seen[2]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, seen[2]), vpiNullOp);
}

// D3: the vpiConstraintExpr iteration returns the body expressions of a
// container constraint expression in the order they occur. Here the container
// is an implication whose body holds three constraint expressions; the
// iteration hands them back in source order.
TEST_F(ConstraintExpression, ConstraintExprIterationReturnsBodyInOrder) {
  VpiObject e0;
  e0.type = vpiConstraintExpr;
  VpiObject e1;
  e1.type = vpiDistribution;
  VpiObject e2;
  e2.type = vpiConstraintExpr;

  VpiObject implication;
  implication.type = vpiImplication;
  implication.constraint_exprs = {&e0, &e1, &e2};

  vpiHandle it = vpi_iterate(vpiConstraintExpr, &implication);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(seen[0], &e0);  // occurrence order is preserved
  EXPECT_EQ(seen[1], &e1);
  EXPECT_EQ(seen[2], &e2);
}

// D3: the body walk fires for every container kind the Detail names - an
// implication, a constraint if, a constraint if-else, and a foreach - so each
// reaches its own body list through vpiConstraintExpr.
TEST_F(ConstraintExpression, ConstraintExprIterationFiresForEachContainerKind) {
  for (int kind :
       {vpiImplication, vpiConstrIf, vpiConstrIfElse, vpiConstrForEach}) {
    VpiObject body;
    body.type = vpiConstraintExpr;

    VpiObject container;
    container.type = kind;
    container.constraint_exprs = {&body};

    vpiHandle it = vpi_iterate(vpiConstraintExpr, &container);
    ASSERT_NE(it, nullptr) << "container kind " << kind;
    EXPECT_EQ(vpi_scan(it), &body) << "container kind " << kind;
    EXPECT_EQ(vpi_scan(it), nullptr) << "container kind " << kind;
  }
}

// D3: the dedicated body walk is scoped to the container kinds. A constraint
// expression that is not a container (here a distribution) does not expose a
// body through vpiConstraintExpr, so the iteration falls back to the generic
// child match and finds nothing when no such child is present.
TEST_F(ConstraintExpression, ConstraintExprIterationScopedToContainerKinds) {
  VpiObject stray_body;
  stray_body.type = vpiConstraintExpr;

  VpiObject distribution;
  distribution.type = vpiDistribution;
  // A body list on a non-container is ignored: the special walk does not fire.
  distribution.constraint_exprs = {&stray_body};

  EXPECT_EQ(vpi_iterate(vpiConstraintExpr, &distribution), nullptr);
}

// D3: a container that holds no body expressions has nothing to walk, so its
// vpiConstraintExpr iteration yields a null iterator even though the special
// container walk does fire for its kind.
TEST_F(ConstraintExpression,
       ConstraintExprIterationEmptyWhenContainerHasNoBody) {
  VpiObject implication;
  implication.type =
      vpiImplication;  // a container kind, but with an empty body

  EXPECT_EQ(vpi_iterate(vpiConstraintExpr, &implication), nullptr);
}

}  // namespace
}  // namespace delta
