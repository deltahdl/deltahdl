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

// §24.5 bars "calling program subroutines from within design modules", and a
// program subroutine is one declared in a program. §23.9 decides which
// declaration a call reaches -- "If it is declared locally, then the local item
// shall be used" -- and it lists a begin-end block among the scopes a
// declaration can be local to, so `p.go()` under a block-local `p` calls that
// object's method and reaches the nested program not at all.
//
// The rule resolved nothing: IsProgramSubroutineCallExpr matched the leftmost
// component of the callee against the set of program instance names, so this
// legal source was refused. The local carries the program's name deliberately;
// one named anything else cannot fail.
TEST(ProgramSubroutineCall,
     ABlockLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    pkt p;\n"
      "    p.go();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same shadow written one block deeper, so the narrowing has to survive the
// descent into a nested begin-end rather than holding only in the block the
// procedural item itself carries. §23.9 makes every begin-end block a scope, so
// the inner block's `p` is what the call standing beside it reaches.
TEST(ProgramSubroutineCall,
     ANestedBlockLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    begin\n"
      "      pkt p;\n"
      "      p.go();\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The true positive beside the two acceptances above: the same call with the
// shadowing declaration taken out, so `p.go` reaches the nested program's task
// and §24.5 applies. A fix that silenced the rule wherever a method call
// appeared would pass both cases above and fail this one, which is what makes
// the three a set rather than two acceptances.
TEST(ProgramSubroutineCall,
     AProgramSubroutineCallWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    p.go();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            9, "24.5"));
}

// §24.5 says "Calling program subroutines from within design modules is illegal
// and shall result in an error" and names no position the call may stand in. A
// task the module declares is within the design module, so a call written there
// is one the sentence reaches. The rule read a continuous assignment and the
// body of a procedural block and nothing else, and a task's statements are in
// neither, so this source elaborated clean.
TEST(ProgramSubroutineCall, AProgramSubroutineCallInAModuleTaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work();\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

// A function beside the task above. The two item kinds are separate
// ModuleItemKind values reaching the walk through one branch, so a fix keyed on
// the task alone would leave the function unreported.
TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInAModuleFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  function int work();\n"
      "    p.go();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

// The acceptance beside the two above: §23.9 makes the task a scope of its own,
// so a declaration at the head of its body is what `p.go()` calls a method of,
// and the program's task is not reached. The walk added for the subroutine body
// is WalkSubroutineBodyForProgramCall, which erases such a declaration before
// reading the body; one that walked the body with the module's set unnarrowed
// would pass the two cases above and fail this one.
TEST(ProgramSubroutineCall,
     ASubroutineLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work();\n"
      "    pkt p;\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A formal argument shadows the same way, and reaches the body in func_args
// rather than in func_body_stmts, so the two acceptances stand for the two
// erases WalkSubroutineBodyForProgramCall makes.
TEST(ProgramSubroutineCall,
     AFormalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work(pkt p);\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §24.5 says "Calling program subroutines from within design modules is illegal
// and shall result in an error" and names no position the call may stand in. A
// class declared in the module is within that design module, so a method of it
// is reached exactly as a task of the module is. The rule read the module's
// items and no class among them, so this source elaborated clean.
TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInAModuleClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class driver;\n"
      "    function void run();\n"
      "      p.go();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            7, "24.5"));
}

// The acceptance beside it: §23.9 makes the method a scope of its own, so the
// handle declared at the head of its body is what `p.go()` calls a method of
// and the program's task is not reached. The class route reads the method
// through WalkSubroutineBodyForProgramCall, which erases that declaration.
TEST(ProgramSubroutineCall,
     AMethodLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class driver;\n"
      "    function void run();\n"
      "      pkt p;\n"
      "      p.go();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.9 makes a class nested in a class a scope within the enclosing one, so a
// method of it is within the design module exactly as a method of the outer
// class is, which is what §24.5 reaches. ClassMember carries a nested class in
// nested_class rather than in the class_decl of a method, so the class arm
// followed methods alone and stopped at the outer class.
TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInANestedClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        p.go();\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            8, "24.5"));
}

// The acceptance beside it: the nested class reaches the same subroutine
// helper, so the handle declared at the head of the body still shadows the
// program instance name.
TEST(ProgramSubroutineCall,
     ANestedClassMethodLocalOfAProgramInstanceNameIsNotASubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        pkt p;\n"
      "        p.go();\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
