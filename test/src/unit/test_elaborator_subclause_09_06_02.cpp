#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DisableStatementElaboration, DisableNamedBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "    disable blk;\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableFromOtherProcessElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin : outer\n"
      "    forever @(posedge clk) x = x + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #100;\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->processes.size(), 2u);
}

TEST(DisableStatementElaboration, DisableFunctionRejectsWithError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    disable my_func;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "disable statement shall not be used to disable a function", 6, "9.6.2"));
}

TEST(DisableStatementElaboration, DisableNamedBlockInFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(input int x);\n"
      "    begin : blk\n"
      "      if (x == 0) disable blk;\n"
      "    end\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterBlockFromNestedBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "      disable outer;\n"
      "    end\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableAutoTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic my_task;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterBlockFromInsideFunctionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  function int f(input int x);\n"
      "    disable outer_blk;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin : outer_blk\n"
      "    int r;\n"
      "    r = f(1);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableStatementElaboration, DisableOuterTaskFromInsideFunctionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(input int x);\n"
      "    disable t;\n"
      "    return x;\n"
      "  endfunction\n"
      "  task t;\n"
      "    int r;\n"
      "    r = f(1);\n"
      "  endtask\n"
      "  initial t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.2 bars a disable statement that names a function and puts no condition
// on where that statement stands, so every position a statement holds a
// statement in is a position the report is made at. CheckDisableTargets in
// src/elaborator/elaborator_validate_matches.cpp had written out eight of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each. Stmt::for_inits and
// Stmt::for_steps are the two remaining ones and get no case: A.6.8 admits only
// a variable assignment or a declaration there, so a disable statement cannot
// be written in either.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(DisableStatementElaboration,
     DisableFunctionInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic ok;\n"
      "  initial assert (ok) disable my_func;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "disable statement shall not be used to disable a function", 6, "9.6.2"));
}

TEST(DisableStatementElaboration,
     DisableFunctionInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic ok;\n"
      "  initial assert (ok) else disable my_func;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "disable statement shall not be used to disable a function", 6, "9.6.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(DisableStatementElaboration,
     DisableFunctionInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { disable my_func; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "disable statement shall not be used to disable a function", 7, "9.6.2"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(DisableStatementElaboration,
     DisableFunctionInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int my_func(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { disable my_func; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "disable statement shall not be used to disable a function", 8, "9.6.2"));
}

}  // namespace
