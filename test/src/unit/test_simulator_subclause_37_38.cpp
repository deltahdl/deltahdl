#include <gtest/gtest.h>

#include <cstddef>
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
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.38 Constraint expression: the VPI object model for a constraint
// expression - the group spanning an implication, a constraint if / if-else, a
// foreach constraint, a distribution, a bare (optionally soft) expression, and
// a soft disable. The soft-disable expr edge and the foreach distribution edge
// are served by the generic object-model and §38 traversal routines. This
// clause's own rules are its three numbered Details, and the tests below
// observe the production code that applies them, together with the two figure
// edges that reach nothing without a rule of their own - the vpiCondition of a
// guarded constraint and the vpiElseConst of a constraint if-else:
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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&foreach))),
            &array);
}

// D1: the relation is specific to a foreach constraint and reports NULL when no
// array is attached; it does not pick up a stray variable on another object
// kind. A non-foreach object with a vpiVariables-typed child is unaffected by
// the foreach case and still resolves through the generic walk.
TEST_F(ConstraintExpression, ForeachVariablesIsScopedAndNullWhenAbsent) {
  VpiObject foreach;
  foreach
    .type = vpiConstrForEach;  // no array attached
  EXPECT_EQ(vpi_handle(vpiVariables, VpiHandleOf(&foreach)), nullptr);

  // The foreach Handle case does not fire for a different object kind: an
  // implication leaves vpiVariables to the generic traversal, which finds a
  // child whose own type is literally vpiVariables.
  VpiObject vars_child;
  vars_child.type = vpiVariables;
  VpiObject implication;
  implication.type = vpiImplication;
  implication.children = {&vars_child};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&implication))),
            &vars_child);
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

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);  // every position is reported, in order
  EXPECT_EQ(VpiObjectOf(seen[0]), &var_i);  // left-to-right order is preserved
  EXPECT_EQ(VpiObjectOf(seen[2]), &var_k);
  EXPECT_NE(VpiObjectOf(seen[1]),
            &var_i);  // the skipped slot is a fresh placeholder
  EXPECT_NE(VpiObjectOf(seen[1]), &var_k);
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

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_i);
  EXPECT_EQ(vpi_scan(it), nullptr);

  VpiObject empty_foreach;
  empty_foreach.type = vpiConstrForEach;  // no loop vars
  EXPECT_EQ(vpi_iterate(vpiLoopVars, VpiHandleOf(&empty_foreach)), nullptr);
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

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[1]), &var_j);  // the present index keeps its slot
  EXPECT_NE(seen[0], seen[2]);              // each skip is its own placeholder
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

  vpiHandle it = vpi_iterate(vpiConstraintExpr, VpiHandleOf(&implication));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);

  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &e0);  // occurrence order is preserved
  EXPECT_EQ(VpiObjectOf(seen[1]), &e1);
  EXPECT_EQ(VpiObjectOf(seen[2]), &e2);
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

    vpiHandle it = vpi_iterate(vpiConstraintExpr, VpiHandleOf(&container));
    ASSERT_NE(it, nullptr) << "container kind " << kind;
    EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &body) << "container kind " << kind;
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

  EXPECT_EQ(vpi_iterate(vpiConstraintExpr, VpiHandleOf(&distribution)),
            nullptr);
}

// D3: a container that holds no body expressions has nothing to walk, so its
// vpiConstraintExpr iteration yields a null iterator even though the special
// container walk does fire for its kind.
TEST_F(ConstraintExpression,
       ConstraintExprIterationEmptyWhenContainerHasNoBody) {
  VpiObject implication;
  implication.type =
      vpiImplication;  // a container kind, but with an empty body

  EXPECT_EQ(vpi_iterate(vpiConstraintExpr, VpiHandleOf(&implication)), nullptr);
}

// The figure's vpiCondition edge. An implication, a constraint if and a
// constraint if-else are each guarded by an expression the figure draws
// vpiCondition to. None of the three was named by the condition resolver, so
// the relation fell through to a walk looking for a child whose own type is the
// vpiCondition tag - a type no object has - and reached nothing.
TEST_F(ConstraintExpression, ConditionReachesTheGuardingExpression) {
  for (int kind : {vpiImplication, vpiConstrIf, vpiConstrIfElse}) {
    VpiObject condition;
    condition.type = vpiOperation;
    VpiObject body;
    body.type = vpiOperation;

    VpiObject guarded;
    guarded.type = kind;
    guarded.children = {&condition};
    guarded.constraint_exprs = {&body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&guarded))),
              &condition)
        << "constraint kind " << kind;
  }
}

// The same edge is drawn on no other constraint expression: a distribution, a
// soft disable and a bare expression are not guarded by a condition.
TEST_F(ConstraintExpression, ConditionIsScopedToTheGuardedKinds) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject dist;
  dist.type = vpiDistribution;
  dist.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&dist)), nullptr);
}

// The figure's vpiElseConst edge. A constraint if-else has two branches, and
// vpiConstraintExpr reaches the then branch, so the else branch is drawn as a
// relation of its own. Nothing recognized it, so the else branch's expressions
// were reachable from the if-else by nothing.
TEST_F(ConstraintExpression, ElseConstReachesTheElseBranchInOrder) {
  VpiObject then_expr;
  then_expr.type = vpiOperation;
  VpiObject else_first;
  else_first.type = vpiOperation;
  VpiObject else_second;
  else_second.type = vpiOperation;

  VpiObject if_else;
  if_else.type = vpiConstrIfElse;
  if_else.constraint_exprs = {&then_expr};
  if_else.else_constraint_exprs = {&else_first, &else_second};

  vpiHandle itr = vpi_iterate(vpiElseConst, VpiHandleOf(&if_else));
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &else_first);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &else_second);
  EXPECT_EQ(vpi_scan(itr), nullptr);

  // D3 is unchanged by it: vpiConstraintExpr still reaches the then branch
  // alone, which is what makes the two branches two sets of expressions.
  vpiHandle body = vpi_iterate(vpiConstraintExpr, VpiHandleOf(&if_else));
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(body)), &then_expr);
  EXPECT_EQ(vpi_scan(body), nullptr);
}

// The else branch belongs to the if-else alone: a constraint if has one branch,
// so the relation reaches nothing from it.
TEST_F(ConstraintExpression, ElseConstIsScopedToTheIfElse) {
  VpiObject branch;
  branch.type = vpiOperation;

  VpiObject constr_if;
  constr_if.type = vpiConstrIf;
  constr_if.else_constraint_exprs = {&branch};

  vpiHandle itr = vpi_iterate(vpiElseConst, VpiHandleOf(&constr_if));
  EXPECT_TRUE(itr == nullptr || vpi_scan(itr) == nullptr);
}

// §37.38 (figure): a guarded constraint reaches its condition through
// vpiCondition. A null handle has none, nor does an implication holding no
// expression child, a typespec among its children not being one.
TEST(ConstraintCondition, NoConditionWithoutAnExpressionChild) {
  EXPECT_EQ(VpiConstraintConditionExpr(nullptr), nullptr);
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject implication;
  implication.type = vpiImplication;
  implication.children = {&typespec};
  EXPECT_EQ(VpiConstraintConditionExpr(&implication), nullptr);
}

// A design run with a PLI application registered, whose constraints' items are
// read back from the model the run built.
class ConstraintExpressionsOfARun : public VpiDesignRun {
 protected:
  // What `ref` iterates through `type`, in the iteration's order.
  static std::vector<vpiHandle> All(int type, vpiHandle ref) {
    std::vector<vpiHandle> all;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return all;
    while (vpiHandle obj = vpi_scan(it)) all.push_back(obj);
    return all;
  }

  // The operand at `index` of the operation `op`.
  static VpiObject* Operand(vpiHandle op, std::size_t index) {
    const std::vector<vpiHandle> kOperands = All(vpiOperand, op);
    return index < kOperands.size() ? VpiObjectOf(kOperands[index]) : nullptr;
  }
};

// §37.34 detail 5 with §37.38: a constraint holds a constraint expression per
// one its block writes, in order: an expression, written soft or not (a name
// standing alone being the variable it names), an implication, a constr if, a
// constr if else, a constr foreach and a soft disable. A uniqueness
// constraint, which §37.38 draws no object for, is none of them (#5840).
TEST_F(ConstraintExpressionsOfARun, AConstraintHoldsItsExpressionsInOrder) {
  Run("module top;\n"
      "  class C; rand int x, y; rand bit b;\n"
      "    constraint c {\n"
      "      soft x > 0; soft b; y < 9;\n"
      "      x < 5 -> x != 3;\n"
      "      if (b) y > 1;\n"
      "      if (y > 2) x > 2; else x < 2;\n"
      "      unique { x, y };\n"
      "      disable soft x;\n"
      "    }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiConstraint, Named(vpiClassDefn, By("top"), "C"), "c");
  ASSERT_NE(c, nullptr);
  const std::vector<vpiHandle> kItems = All(vpiConstraintItem, c);
  std::vector<int> types;
  types.reserve(kItems.size());
  for (vpiHandle item : kItems) types.push_back(vpi_get(vpiType, item));
  EXPECT_EQ(types, (std::vector<int>{vpiOperation, vpiBitVar, vpiOperation,
                                     vpiImplication, vpiConstrIf,
                                     vpiConstrIfElse, vpiSoftDisable}));
  ASSERT_EQ(kItems.size(), 7u);
  EXPECT_EQ(vpi_get(vpiSoft, kItems[0]), 1);
  EXPECT_EQ(vpi_get(vpiSoft, kItems[2]), 0);
  // An implication and a constr if reach their guards through vpiCondition,
  // a name standing alone among them, and what they govern through
  // vpiConstraintExpr; an if-else's else branch is reached apart.
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiCondition, kItems[3])),
            vpiOperation);
  EXPECT_EQ(All(vpiConstraintExpr, kItems[3]).size(), 1u);
  vpiHandle guard = vpi_handle(vpiCondition, kItems[4]);
  ASSERT_NE(guard, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, guard), "b");
  EXPECT_EQ(All(vpiConstraintExpr, kItems[5]).size(), 1u);
  EXPECT_EQ(All(vpiElseConst, kItems[5]).size(), 1u);
  EXPECT_EQ(All(vpiElseConst, kItems[4]).size(), 0u);
}

// §8.13 with §37.38: a name in a constraint of a class finds the class's
// property, one the class inherits among them, and else a declaration of the
// module declaring the class (#5840).
TEST_F(ConstraintExpressionsOfARun, AConstraintsNamesFindTheClassFirst) {
  Run("module top; int m, x;\n"
      "  class B; rand int y; endclass\n"
      "  class C extends B; rand int x;\n"
      "    constraint c { x < y; y < m; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle c = Named(vpiConstraint, defn, "c");
  ASSERT_NE(c, nullptr);
  const std::vector<vpiHandle> kItems = All(vpiConstraintItem, c);
  ASSERT_EQ(kItems.size(), 2u);
  vpiHandle y = Named(vpiVariables, Named(vpiClassDefn, By("top"), "B"), "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(Operand(kItems[0], 0), VpiObjectOf(Named(vpiVariables, defn, "x")));
  EXPECT_EQ(Operand(kItems[0], 1), VpiObjectOf(y));
  EXPECT_EQ(Operand(kItems[1], 1), VpiObjectOf(By("top.m")));
}

// §37.38 details 1 and 2: a constr foreach reaches the array it indexes
// through vpiVariables and its index variables through vpiLoopVars, a skipped
// one standing as a null operation; a name in its body finds the index
// variables first, ahead of a property of the class of the same name (#5840).
TEST_F(ConstraintExpressionsOfARun, AForeachConstraintReachesItsArray) {
  Run("module top;\n"
      "  class C; rand int a[2][2], j;\n"
      "    constraint c { foreach (a[, j]) j < 2; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kItems =
      All(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 1u);
  vpiHandle loop = kItems[0];
  EXPECT_EQ(vpi_get(vpiType, loop), vpiConstrForEach);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, loop)),
            VpiObjectOf(Named(vpiVariables, defn, "a")));
  const std::vector<vpiHandle> kIndices = All(vpiLoopVars, loop);
  ASSERT_EQ(kIndices.size(), 2u);
  EXPECT_EQ(vpi_get(vpiOpType, kIndices[0]), vpiNullOp);
  EXPECT_STREQ(vpi_get_str(vpiName, kIndices[1]), "j");
  const std::vector<vpiHandle> kBody = All(vpiConstraintExpr, loop);
  ASSERT_EQ(kBody.size(), 1u);
  EXPECT_EQ(Operand(kBody[0], 0), VpiObjectOf(kIndices[1]));
}

// §18.7 with §37.38: a name in a randomize call's inline constraint block
// finds the randomized object's class's property ahead of a declaration of the
// module, and else a declaration of the block the call stands in. A call on
// an object of a class the design does not declare finds the scope's only
// (#5840).
TEST_F(ConstraintExpressionsOfARun, AnInlineBlocksNamesFindTheClassFirst) {
  Run("module top; int x;\n"
      "  class C; rand int x; endclass\n"
      "  C h = new;\n"
      "  initial begin : b int lim;\n"
      "    void'(h.randomize() with { x < lim; });\n"
      "    void'(process::self().randomize() with { x < lim; });\n"
      "  end\n"
      "endmodule\n");
  std::vector<vpiHandle> constraints;
  for (vpiHandle call : All(vpiStmt, By("top.b"))) {
    constraints.push_back(vpi_handle(vpiWith, call));
  }
  ASSERT_EQ(constraints.size(), 2u);
  ASSERT_NE(constraints[0], nullptr);
  ASSERT_NE(constraints[1], nullptr);
  const std::vector<vpiHandle> kOwn = All(vpiConstraintItem, constraints[0]);
  ASSERT_EQ(kOwn.size(), 1u);
  EXPECT_EQ(Operand(kOwn[0], 0),
            VpiObjectOf(
                Named(vpiVariables, Named(vpiClassDefn, By("top"), "C"), "x")));
  EXPECT_EQ(Operand(kOwn[0], 1), VpiObjectOf(By("top.b.lim")));
  const std::vector<vpiHandle> kScopes = All(vpiConstraintItem, constraints[1]);
  ASSERT_EQ(kScopes.size(), 1u);
  EXPECT_EQ(Operand(kScopes[0], 0), VpiObjectOf(By("top.x")));
}

// §37.33 with §37.38: a name in a constraint of a class obj finds the
// object's variable (#5840).
TEST_F(ConstraintExpressionsOfARun, AClassObjsConstraintFindsItsVariables) {
  Run("module top; int m;\n"
      "  class C; rand int x; constraint c { x < m; } endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  ASSERT_NE(obj, nullptr);
  const std::vector<vpiHandle> kItems =
      All(vpiConstraintItem, Named(vpiConstraint, obj, "c"));
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(Operand(kItems[0], 0), VpiObjectOf(Named(vpiVariables, obj, "x")));
  EXPECT_EQ(Operand(kItems[0], 1), VpiObjectOf(By("top.m")));
}

// §18.5.9 with §37.34: a solve-before item is a constraint ordering among a
// constraint's items, reaching the expressions it solves before through
// vpiSolveBefore and those it solves after through vpiSolveAfter, each in the
// order written (#5842).
TEST_F(ConstraintExpressionsOfARun, ASolveBeforeItemIsAConstraintOrdering) {
  Run("module top;\n"
      "  class C; rand int x, y, z;\n"
      "    constraint c { solve x, y before z; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kItems =
      All(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiConstraintOrdering);
  std::vector<std::string> before;
  for (vpiHandle expr : All(vpiSolveBefore, kItems[0])) {
    before.emplace_back(vpi_get_str(vpiName, expr));
  }
  EXPECT_EQ(before, (std::vector<std::string>{"x", "y"}));
  const std::vector<vpiHandle> kAfter = All(vpiSolveAfter, kItems[0]);
  ASSERT_EQ(kAfter.size(), 1u);
  EXPECT_EQ(VpiObjectOf(kAfter[0]),
            VpiObjectOf(Named(vpiVariables, defn, "z")));
  EXPECT_EQ(All(vpiSolveAfter, defn).size(), 0u);
  EXPECT_EQ(All(vpiElseConst, kItems[0]).size(), 0u);
}

// §18.5.3 with §37.34 and §37.38: a dist item of a constraint block is a
// distribution among the constraint's items, reaching the expression it
// weights and a dist item per entry, in order. A dist item reaches its value,
// or the range [lo:hi] it gives, through vpiValueRange, its weight through
// vpiWeight, and reports := as vpiEqualDist and :/ as vpiDivDist. A default
// item and a range about a centre reach no value range, and an item written
// with no weight no weight (#5843).
TEST_F(ConstraintExpressionsOfARun, ADistItemIsADistribution) {
  Run("module top;\n"
      "  class C; rand int x;\n"
      "    constraint c {\n"
      "      x dist { 0 := 2, [1:3] :/ 4, 7, [9 +/- 1] := 1, default :/ 5 };\n"
      "    }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  const std::vector<vpiHandle> kItems =
      All(vpiConstraintItem, Named(vpiConstraint, defn, "c"));
  ASSERT_EQ(kItems.size(), 1u);
  vpiHandle dist = kItems[0];
  EXPECT_EQ(vpi_get(vpiType, dist), vpiDistribution);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, dist)),
            VpiObjectOf(Named(vpiVariables, defn, "x")));
  const std::vector<vpiHandle> kEntries = All(vpiDistItem, dist);
  ASSERT_EQ(kEntries.size(), 5u);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[0]), vpiEqualDist);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[1]), vpiDivDist);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiValueRange, kEntries[0])),
            vpiConstant);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiWeight, kEntries[0])), vpiConstant);
  vpiHandle range = vpi_handle(vpiValueRange, kEntries[1]);
  ASSERT_NE(range, nullptr);
  EXPECT_EQ(vpi_get(vpiType, range), vpiRange);
  EXPECT_NE(vpi_handle(vpiLeftRange, range), nullptr);
  EXPECT_NE(vpi_handle(vpiRightRange, range), nullptr);
  EXPECT_EQ(vpi_handle(vpiWeight, kEntries[2]), nullptr);
  EXPECT_EQ(vpi_handle(vpiValueRange, kEntries[3]), nullptr);
  EXPECT_EQ(vpi_handle(vpiValueRange, kEntries[4]), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiWeight, kEntries[4])), vpiConstant);
  EXPECT_EQ(vpi_handle(vpiCondition, kEntries[0]), nullptr);
}

// §37.19 with §37.38: a select through two unpacked dimensions of a class's
// array property, written as a size or as a range either way, is a var select
// of a var select, in a constraint of the class defn and of a class obj
// alike; one through a dynamic array's one dimension is a var select too
// (#5844).
TEST_F(ConstraintExpressionsOfARun, ASelectThroughAPropertysDimensions) {
  Run("module top;\n"
      "  class C; rand int a[2][2], b[3:0][1:2], d[];\n"
      "    constraint c {\n"
      "      foreach (a[i, j]) a[i][j] > 0;\n"
      "      foreach (b[i, j]) b[i][j] > 0;\n"
      "      foreach (d[k]) d[k] > 0;\n"
      "    }\n"
      "  endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  ASSERT_NE(obj, nullptr);
  for (vpiHandle holder : {defn, obj}) {
    const std::vector<vpiHandle> kLoops =
        All(vpiConstraintItem, Named(vpiConstraint, holder, "c"));
    ASSERT_EQ(kLoops.size(), 3u);
    for (vpiHandle loop : kLoops) {
      const std::vector<vpiHandle> kBody = All(vpiConstraintExpr, loop);
      ASSERT_EQ(kBody.size(), 1u);
      VpiObject* select = Operand(kBody[0], 0);
      ASSERT_NE(select, nullptr);
      EXPECT_EQ(select->type, vpiVarSelect);
    }
  }
}

}  // namespace
}  // namespace delta
