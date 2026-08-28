#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProgramSubroutineCall, ModuleCallingProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  initial p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            5, "24.5"));
}

// §24.5 says "program subroutines" -- the illegal-from-design rule covers
// functions as well as tasks. A design module calling a program function in an
// expression position must also be rejected.
TEST(ProgramSubroutineCall, ModuleCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p;\n"
      "    function int pfunc; return 7; endfunction\n"
      "  endprogram\n"
      "  initial x = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  // The source also draws the §24.3 hierarchical-reference report; this names
  // the §24.5 call rule the test is written for.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

// §24.5: the illegal-call rule reaches a program function invoked from a
// continuous assignment in a design module. This travels a distinct elaborator
// code path from the procedural-body cases above (the continuous-assign walker
// rather than the statement walker), so it needs its own coverage.
TEST(ProgramSubroutineCall, ModuleContAssignCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] w;\n"
      "  program p;\n"
      "    function logic [7:0] pfunc; return 8'd3; endfunction\n"
      "  endprogram\n"
      "  assign w = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  // The continuous-assign walker reports at the item's own location, which is
  // the `assign` keyword on line 6.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ProgramCallingOtherProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p1;\n"
      "    task p1task(input int v); x = v; endtask\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial p1.p1task(9);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.5: a program may also call a subroutine declared in a design module. The
// illegal-call check keys off the caller's scope, so it must stay silent when a
// program invokes a task belonging to the enclosing design module.
TEST(ProgramSubroutineCall, ProgramCallingDesignModuleTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  task dtask(input int v); x = v; endtask\n"
      "  program p;\n"
      "    initial dtask(5);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.5 says "Calling program subroutines from within design modules is illegal
// and shall result in an error" and names no position the call is allowed in,
// so every position a statement holds a statement in is one the report reaches.
// WalkStmtForProgramCall in
// src/elaborator/elaborator_validate_hier_refs.cpp had written out nine of
// the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h.
// The four cases below stand in the four positions it was missing, each of
// which elaborated clean beforehand with the illegal call left unreported.

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(ProgramSubroutineCall, ProgramTaskCallInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic ok;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  initial assert (ok) p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(ProgramSubroutineCall, ProgramTaskCallInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic armed;\n"
      "  program pr;\n"
      "    task drain; endtask\n"
      "  endprogram\n"
      "  initial assert (armed) else pr.drain();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §24.5 is
// a rule about where the call is written rather than about whether it runs, so
// the report stands whether the weighted draw would select the item or not.
TEST(ProgramSubroutineCall, ProgramTaskCallInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pk;\n"
      "    task pick; endtask\n"
      "  endprogram\n"
      "  initial randcase 1: pk.pick(); endcase\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            5, "24.5"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ProgramSubroutineCall, ProgramTaskCallInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program ps;\n"
      "    task sample; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ps.sample(); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            7, "24.5"));
}

}  // namespace
