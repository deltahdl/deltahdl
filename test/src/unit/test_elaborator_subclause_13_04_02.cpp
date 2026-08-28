#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeElaboration, DefaultLifetimeFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, RecursiveAutomaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.2: "Automatic function items cannot be accessed by hierarchical
// references." A path into an automatic function's local is rejected, and the
// report names §13.4.2 rather than §13.3.1, which states the same sentence for
// a task and is a different rule about a different construct.
TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

// Contrast: a static function allocates its items statically, so the same
// hierarchical path is permitted and the §13.4.2 restriction must not fire.
TEST(FunctionLifetimeElaboration, StaticFunctionItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function static int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The restriction also applies to references from within procedural blocks.
TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

// §13.4.2 says "Automatic function items cannot be accessed by hierarchical
// references" and names no position such a reference is allowed to stand in,
// so every position a statement holds a statement in is one the report reaches.
// WalkStmtsForAutoRef in
// src/elaborator/elaborator_validate_hier_refs.cpp had written out nine of
// the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h.
// The four cases below stand in the four positions it was missing, once for
// this clause's report; the same four for §13.3.1's task report are in
// test/src/unit/test_elaborator_subclause_13_03_01.cpp, which is a different
// rule about a different construct and a report of its own.

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInAnAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial assert (ok) y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 8, "13.4.2"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInAnAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic held;\n"
      "  logic armed;\n"
      "  function automatic int drain();\n"
      "    int depth;\n"
      "    return depth;\n"
      "  endfunction\n"
      "  initial assert (armed) else held = drain.depth;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 8, "13.4.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §13.4.2
// bars the reference rather than the execution, so the report stands whether
// the weighted draw would select the item or not.
TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInARandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic taken;\n"
      "  function automatic int pick();\n"
      "    int chosen;\n"
      "    return chosen;\n"
      "  endfunction\n"
      "  initial randcase 1: taken = pick.chosen; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInARandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic kept;\n"
      "  function automatic int sample();\n"
      "    int sampled;\n"
      "    return sampled;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = sample.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 9, "13.4.2"));
}

}  // namespace
