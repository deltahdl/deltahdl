#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.75 Do-while, foreach: the VPI object model for a do-while statement and a
// foreach statement. The clause carries two diagrams and two numbered Details.
//
// The do-while diagram draws a controlling condition expression (vpiCondition)
// and an unlabeled edge to the dotted `stmt` enclosure, which §37.4.3 names
// vpiStmt and which is the body the loop runs. As with the other looping and
// conditional statements (§37.66/§37.71/§37.74), the condition's own type is an
// expression kind rather than the vpiCondition relation tag, so it needs
// dedicated production code. So does the body: §37.4.1 makes a dotted enclosure
// a class grouping other objects and classes rather than a kind, so the body
// carries the kind a statement of a design carries - a begin, an assignment,
// another loop - and never vpiStmt, and read the other way the relation reached
// the body of no do-while and no foreach that could be written.
//
// The foreach diagram draws the indexed variable (vpiVariables), the loop's
// index variables (vpiLoopVars), and the same unlabeled edge to a body. Its
// two Details are this clause's own rules:
//   D1 - the variable reached from a foreach statement via vpiVariables
//        represents the packed array, unpacked array, or string var being
//        indexed (the designated-pointer Handle case).
//   D2 - the vpiLoopVars iteration returns the foreach statement's index
//        variables in left-to-right order, with a skipped position reported as
//        a vpiOperation whose vpiOpType is vpiNullOp (the dedicated loop-var
//        walk of Iterate, shared with the foreach constraint of §37.38).
//
// The tests below observe the production code applying each rule through the
// public vpi_handle/vpi_iterate/vpi_scan/vpi_get entry points.

// The fixture installs a context so the public dispatch runs over the test
// objects.
class DoWhileForeach : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Do-while condition edge (vpiCondition -> expr): a do-while statement reaches
// its controlling condition through the public vpi_handle(vpiCondition, ...)
// dispatch. The scan is type-directed: it skips the body statement and returns
// the condition expression rather than the first child.
TEST_F(DoWhileForeach, DoWhileReachesConditionAmongConditionAndBody) {
  VpiObject body;
  body.type = vpiBegin;  // the body, a kind the `stmt` class groups, first
  VpiObject condition;
  condition.type = vpiOperation;  // the condition: an expression kind

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body, &condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&do_while))),
            &condition);
}

// Do-while condition reports no expression when the statement carries no
// condition child: the scan finds no expression among the statement-edge
// children and returns null.
TEST_F(DoWhileForeach, DoWhileWithoutConditionReportsNoCondition) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&do_while)), nullptr);
}

// Do-while condition gating: the do-while condition relation is scoped to the
// do-while kind, so it does not disturb the vpiCondition edge other objects
// draw. A non-do-while object carrying an expression child is left to the
// generic traversal, which matches by exact relation tag and so does not
// surface that expression.
TEST_F(DoWhileForeach, DoWhileConditionRelationIsScopedToDoWhile) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_do_while;
  not_a_do_while.type = vpiBegin;  // not a do-while statement
  not_a_do_while.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&not_a_do_while)), nullptr);
}

// Do-while body edge (the diagram's unlabeled arrow to `stmt`): a do-while
// statement reaches its body through the public vpi_handle(vpiStmt, ...)
// dispatch, which skips the condition child and returns the statement - one of
// the kinds the `stmt` class groups, told from the condition by that.
TEST_F(DoWhileForeach, DoWhileReachesBodyThroughVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&condition, &body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&do_while))), &body);
}

// D1: a foreach statement's vpiVariables relation reaches the variable that
// represents the array being indexed - here a packed array variable. That
// variable's own type is a variable kind, so it is held as a designated pointer
// and reached through the scoped Handle case rather than a generic child match.
TEST_F(DoWhileForeach, ForeachStatementVariablesReachesIndexedArray) {
  VpiObject array;
  array.type = vpiPackedArrayVar;  // the packed array the foreach iterates over

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&foreach))),
            &array);
}

// D1: the relation reports NULL when no indexed variable is attached. The
// scoped Handle case still fires for the foreach statement kind, but the
// designated pointer is null, so the relation yields nothing.
TEST_F(DoWhileForeach, ForeachStatementVariablesReportsNoVariableWhenAbsent) {
  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;  // no indexed variable attached

  EXPECT_EQ(vpi_handle(vpiVariables, VpiHandleOf(&foreach)), nullptr);
}

// D1: the foreach-statement vpiVariables case is specific to a foreach
// statement. A different object kind is left to the generic traversal: its
// designated foreach_array pointer is ignored and a child whose own type is
// literally vpiVariables is returned instead.
TEST_F(DoWhileForeach, ForeachStatementVariablesIsScopedToForeachStatements) {
  VpiObject distractor_array;
  distractor_array.type = vpiPackedArrayVar;
  VpiObject vars_child;
  vars_child.type = vpiVariables;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;                    // not a foreach statement
  not_a_foreach.foreach_array = &distractor_array;  // must be ignored here
  not_a_foreach.children = {&vars_child};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&not_a_foreach))),
            &vars_child);
}

// D2: the vpiLoopVars iteration returns the foreach statement's index variables
// in left-to-right order, reached from the statement's dedicated loop-var list
// (not by matching children whose own type is literally vpiLoopVars). A skipped
// index position - stored as a null slot in the list - comes back as a freshly
// built placeholder operation whose operator is the null operation (vpiNullOp),
// so the caller still sees something occupying that slot. The real index
// variables on either side of the skip confirm the left-to-right order.
TEST_F(DoWhileForeach, ForeachStatementSkippedIndexIsNullOpPlaceholder) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;
  VpiObject var_k;
  var_k.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {&var_i, nullptr, &var_k};  // middle index skipped

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_i);
  vpiHandle skipped = vpi_scan(it);
  ASSERT_NE(skipped, nullptr);
  EXPECT_NE(VpiObjectOf(skipped),
            &var_i);  // the skipped slot is a fresh placeholder
  EXPECT_NE(VpiObjectOf(skipped), &var_k);
  EXPECT_EQ(vpi_get(vpiType, skipped), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipped), vpiNullOp);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_k);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// D2 edge case: when several index positions are skipped - here the first and
// the last, surrounding a single named index - each skip is reported as its own
// freshly built null-op placeholder. The two placeholders are distinct objects
// (one per slot), and the named index keeps its middle position, confirming the
// left-to-right walk handles boundary skips and back-to-back placeholder
// construction.
TEST_F(DoWhileForeach,
       ForeachStatementBoundarySkipsEachGetDistinctNullOpPlaceholder) {
  VpiObject var_j;
  var_j.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {nullptr, &var_j, nullptr};  // leading and trailing skip

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);

  vpiHandle first_skip = vpi_scan(it);
  ASSERT_NE(first_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, first_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, first_skip), vpiNullOp);

  EXPECT_EQ(VpiObjectOf(vpi_scan(it)),
            &var_j);  // the named index keeps its middle slot

  vpiHandle last_skip = vpi_scan(it);
  ASSERT_NE(last_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, last_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, last_skip), vpiNullOp);

  EXPECT_NE(first_skip, last_skip);  // each skipped slot is its own placeholder
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Foreach body edge (the diagram's unlabeled arrow to `stmt`): a foreach
// statement reaches its body through the public vpi_handle(vpiStmt, ...)
// dispatch, which returns the statement child. The indexed-variable and
// loop-variable edges are held as the statement's own designated array and
// loop-var list rather than among its children, so neither stands where the
// body is looked for.
TEST_F(DoWhileForeach, ForeachStatementReachesBodyThroughVpiStmt) {
  VpiObject array;
  array.type = vpiPackedArrayVar;  // the indexed variable (its own relation)
  VpiObject body;
  body.type = vpiBegin;  // the body, a kind the `stmt` class groups

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;
  foreach
    .children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&foreach))), &body);
}

// D2: the loop-var iteration is scoped to the foreach statement kind. A
// different object kind carrying a loop-var list does not have it walked: the
// iteration falls to the generic handling, which matches children whose own
// type is literally vpiLoopVars - of which there are none - and so reports
// nothing.
TEST_F(DoWhileForeach,
       ForeachStatementLoopVarsIterationIsScopedToForeachStatements) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;       // not a foreach statement
  not_a_foreach.loop_vars = {&var_i};  // must not be walked here

  EXPECT_EQ(vpi_iterate(vpiLoopVars, VpiHandleOf(&not_a_foreach)), nullptr);
}

// Body edge: both loops reach a body whatever kind it is written as - a lone
// statement, a block, or a nested loop - because what the relation asks for is
// membership of the `stmt` class rather than any one kind.
TEST_F(DoWhileForeach, EachKindABodyCarriesIsReachedByBothLoopKinds) {
  for (int loop_kind : {vpiDoWhile, vpiForeachStmt}) {
    for (int body_kind :
         {vpiAssignment, vpiNamedBegin, vpiFork, vpiDoWhile, vpiNullStmt}) {
      VpiObject body;
      body.type = body_kind;

      VpiObject loop;
      loop.type = loop_kind;
      loop.children = {&body};

      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&loop))), &body)
          << "loop kind " << loop_kind << ", body kind " << body_kind;
    }
  }
}

// Body edge, empty outcome: a do-while carrying only its condition and a
// foreach carrying only the array it indexes each report no body, so neither
// the condition nor the indexed array is handed back in a body's place.
TEST_F(DoWhileForeach, NeitherLoopReportsABodyWhenItCarriesNoStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&do_while)), nullptr);

  VpiObject array;
  array.type = vpiPackedArrayVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&foreach)), nullptr);
}

// The do-while and foreach loops of a run: those a design's procedures write,
// built from the elaborated design rather than by hand (#5008).
class DoWhileAndForeachLoopsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle FirstBody() {
    vpiHandle it = vpi_iterate(vpiProcess, By("top"));
    return it ? vpi_handle(vpiStmt, vpi_scan(it)) : nullptr;
  }

  // The kind of the first index variable of each foreach loop the block
  // `scope` holds, in the order written.
  static std::vector<int> FirstLoopVarKinds(vpiHandle scope) {
    std::vector<int> kinds;
    vpiHandle stmts = vpi_iterate(vpiStmt, scope);
    if (stmts == nullptr) return kinds;
    while (vpiHandle stmt = vpi_scan(stmts)) {
      if (vpi_get(vpiType, stmt) != vpiForeachStmt) continue;
      kinds.push_back(
          vpi_get(vpiType, vpi_scan(vpi_iterate(vpiLoopVars, stmt))));
    }
    return kinds;
  }
};

// A do-while loop reaches the condition it tests and the statement it runs.
TEST_F(DoWhileAndForeachLoopsOfARun, ADoWhileLoopIsAnObjectOfTheRun) {
  Run("module top; int i; initial do i = i + 1; while (i < 3); endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiDoWhile);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiCondition, loop)), vpiLtOp);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
}

// A foreach loop reaches the array it indexes (detail 1), its index
// variables in order with a null operation for one skipped (detail 2), and
// its body.
TEST_F(DoWhileAndForeachLoopsOfARun, AForeachLoopIsAnObjectOfTheRun) {
  Run("module top; int m [2][3]; initial foreach (m[, j]) m[0][j] = j;\n"
      "endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiForeachStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, loop)),
            VpiObjectOf(By("top.m")));
  vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
  ASSERT_NE(vars, nullptr);
  vpiHandle skipped = vpi_scan(vars);
  vpiHandle j = vpi_scan(vars);
  ASSERT_NE(skipped, nullptr);
  ASSERT_NE(j, nullptr);
  EXPECT_EQ(vpi_get(vpiType, skipped), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipped), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiType, j), vpiIntVar);
  EXPECT_STREQ(vpi_get_str(vpiName, j), "j");
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
}

// A name the body of a foreach loop writes for an index variable is that
// variable, which the loop declares (§12.7.3, #5062).
TEST_F(DoWhileAndForeachLoopsOfARun, TheBodyNamesTheLoopsIndexVariable) {
  Run("module top; int k; int a [3]; initial foreach (a[k]) a[k] = k;\n"
      "endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
  ASSERT_NE(vars, nullptr);
  vpiHandle k = vpi_scan(vars);
  ASSERT_NE(k, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, body)), VpiObjectOf(k));
  EXPECT_NE(VpiObjectOf(k), VpiObjectOf(By("top.k")));
}

// §12.7.3: an index variable over an associative array is of the array's
// index type - a string, an integer, an enumeration a typedef names, or the
// byte a block's array is indexed by - and an int over any other (#5064).
TEST_F(DoWhileAndForeachLoopsOfARun, AnIndexVariableIsOfItsArraysIndexType) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  int s [string]; int g [integer]; int e [e_t]; int f [2];\n"
      "  initial foreach (s[i]) begin end\n"
      "  initial foreach (g[i]) begin end\n"
      "  initial foreach (e[i]) begin end\n"
      "  initial foreach (f[i]) begin end\n"
      "  initial begin : b int q [byte]; foreach (q[k]) begin end end\n"
      "endmodule\n");
  std::vector<int> kinds;
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  while (vpiHandle proc = vpi_scan(procs)) {
    vpiHandle loop = vpi_handle(vpiStmt, proc);
    if (loop != nullptr && vpi_get(vpiType, loop) == vpiNamedBegin) {
      vpiHandle held = vpi_iterate(vpiStmt, loop);
      loop = held == nullptr ? nullptr : vpi_scan(held);
    }
    ASSERT_NE(loop, nullptr);
    vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
    ASSERT_NE(vars, nullptr);
    kinds.push_back(vpi_get(vpiType, vpi_scan(vars)));
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiStringVar, vpiIntegerVar, vpiEnumVar,
                                     vpiIntVar, vpiByteVar}));
}

// §12.7.3 with §7.8: over a block's arrays the same holds. Its associative
// arrays indexed by a typedef name and by a class give an enum and a class var,
// while a fixed-size array, sized by a number or by a parameter, a dynamic
// array, an array a typedef declares and a packed array, which writes no
// unpacked dimension, give an int var.
TEST_F(DoWhileAndForeachLoopsOfARun, ABlocksArraysGiveTheirIndexTypes) {
  Run("module top; typedef enum {A, B} e_t; class C; endclass\n"
      "  typedef int arr_t [3]; localparam int N = 2;\n"
      "  initial begin : b\n"
      "    int f [2]; int d []; int t [e_t]; int c [C]; int p [N]; arr_t a;\n"
      "    bit [3:0] v;\n"
      "    foreach (f[i]) begin end\n"
      "    foreach (d[i]) begin end\n"
      "    foreach (t[i]) begin end\n"
      "    foreach (c[i]) begin end\n"
      "    foreach (p[i]) begin end\n"
      "    foreach (a[i]) begin end\n"
      "    foreach (v[i]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiIntVar, vpiIntVar, vpiEnumVar, vpiClassVar,
                              vpiIntVar, vpiIntVar, vpiIntVar}));
}

// §12.7.3 with §7.8: an index variable over a module's associative array
// indexed by a class is a class var, and one over an array a class property
// holds, which the loop names through the object, an int var.
TEST_F(DoWhileAndForeachLoopsOfARun,
       AClassIndexAndAPropertysArrayGiveTheirKinds) {
  Run("module top; class C; int m [2]; endclass\n"
      "  int c [C]; C o = new;\n"
      "  initial foreach (c[i]) begin end\n"
      "  initial foreach (o.m[i]) begin end\n"
      "endmodule\n");
  std::vector<int> kinds;
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  while (vpiHandle proc = vpi_scan(procs)) {
    vpiHandle vars = vpi_iterate(vpiLoopVars, vpi_handle(vpiStmt, proc));
    ASSERT_NE(vars, nullptr);
    kinds.push_back(vpi_get(vpiType, vpi_scan(vars)));
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiClassVar, vpiIntVar}));
}

// §12.7.3 with §8.4: over an array a class property holds, named through the
// object, or through a chain of objects, the index variable is of the
// property's index type, a string var over a string-indexed array; an int var
// over a fixed-size property and over one named through an element select
// (#5773). Over a module's array named through its instance, the index
// variable is of that array's index type, a string var over a string-indexed
// one and an int var over a fixed-size one (#5787).
TEST_F(DoWhileAndForeachLoopsOfARun, APropertysArrayGivesItsIndexType) {
  Run("module sub; int g [2]; int aa [string]; endmodule\n"
      "module top; sub u ();\n"
      "  class H; int a [string]; endclass\n"
      "  class C; int m [string]; int f [2]; H h = new; endclass\n"
      "  C o = new; C objs [2];\n"
      "  initial begin : b objs[0] = new;\n"
      "    foreach (o.m[k]) begin end\n"
      "    foreach (o.h.a[k]) begin end\n"
      "    foreach (o.f[k]) begin end\n"
      "    foreach (objs[0].f[k]) begin end\n"
      "    foreach (u.g[k]) begin end\n"
      "    foreach (u.aa[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiStringVar, vpiIntVar, vpiIntVar,
                              vpiIntVar, vpiStringVar}));
}

// §12.7.3 with §7.2: over an array a structure's member holds, or a property
// of the class a member holds a handle of, the index variable is of that
// array's index type, a string var over a string-indexed one (#5794).
TEST_F(DoWhileAndForeachLoopsOfARun, AStructMembersArrayGivesItsIndexType) {
  Run("module top;\n"
      "  class H; int m [string]; endclass\n"
      "  typedef struct { int n; int aa [string]; H h; } s_t;\n"
      "  s_t s;\n"
      "  initial begin : b s.h = new;\n"
      "    foreach (s.aa[k]) begin end\n"
      "    foreach (s.h.m[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiStringVar}));
}

// §37.75: a null handle has no do-while condition.
TEST_F(DoWhileForeach, DoWhileConditionOfANullHandleIsNull) {
  EXPECT_EQ(VpiDoWhileConditionExpr(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
