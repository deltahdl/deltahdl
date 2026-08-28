#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ParallelBlockElaboration, ForkJoinInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkJoinAnyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkJoinNoneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, EmptyForkJoinElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ReturnInForkJoinErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement is not allowed inside a fork-join block", 4, "9.3.2"));
}

TEST(ParallelBlockElaboration, ReturnNestedInForkErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      begin\n"
      "        return;\n"
      "      end\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement is not allowed inside a fork-join block", 5, "9.3.2"));
}

TEST(ParallelBlockElaboration, ForkWithLocalparamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    fork\n"
      "      localparam int N = 4;\n"
      "      a = N;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    fork\n"
      "      parameter int W = 8;\n"
      "      a = W;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithBeginEndElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 1;\n"
      "        b = 0;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefArgInForkJoinAnyIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration, RefArgInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration, RefArgInPlainForkJoinAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefStaticArgInForkJoinAnyAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref static int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefArgInForkJoinAnyBlockItemInitAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      automatic int copy = v;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2 says "Within a fork-join_any or fork-join_none block, it shall be
// illegal to refer to formal arguments passed by reference other than in the
// initialization value expressions of variables declared in a
// block_item_declaration of the fork, unless the argument is declared ref
// static", and puts no condition on the statement position the reference
// stands in. A randsequence production's code block holds ordinary procedural
// statements, which A.6.12 gives as `rs_code_block ::= { { data_declaration }
// { statement_or_null } }`, and the parser keeps them in RsProd::code_stmts
// and RsRule::weight_code, reached through Stmt::rs_productions. That is the
// thirteenth of the child-statement links src/parser/ast_stmt.h declares, and
// the only one CheckStmtForRefArgs in
// src/elaborator/elaborator_validate_funcbody.cpp did not walk before it took
// its list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. A ref argument written there
// elaborated clean beforehand.
TEST(ParallelBlockElaboration,
     RefArgInARandsequenceCodeBlockInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : { v = 1; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            5, "9.3.2"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it gets its own
// case: the production `a` below assigns nothing, which leaves the weight
// block as the only place the reported reference can stand.
TEST(ParallelBlockElaboration,
     RefArgInARandsequenceWeightCodeBlockInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : a := 5 { v = 1; };\n"
      "        a : { ; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            5, "9.3.2"));
}

// The four cases below cover the child-statement links of Stmt that
// CheckRefArgsInForkBlocks in src/elaborator/elaborator_validate_funcbody.cpp
// reaches for the first time now that it takes its list from ForEachChildStmt
// in src/elaborator/elaborator_validate_internal.h. That walk is the one that
// finds the fork-join_any and fork-join_none blocks §9.3.2 governs, and it had
// written out eight of the thirteen links: Stmt::assert_pass_stmt,
// Stmt::assert_fail_stmt and the two statement lists Stmt::rs_productions holds
// were missing, so a ref argument used inside a fork written in one of them
// elaborated clean. Stmt::for_inits and Stmt::for_steps were missing too and
// get no case, A.6.8 admitting no par_block in either.
//
// The cases above cover a ref argument written in a new position inside a fork
// the walk already found. These cover the fork itself standing in a new
// position, which is a different link of a different walk.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. A.6.3 makes a
// par_block a statement, so a fork stands in either arm. This case and the next
// cover one arm each.
TEST(ParallelBlockElaboration,
     ForkJoinNoneInAnAssertionPassStmtRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    assert (1) fork v = 1; join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            3, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ForkJoinNoneInAnAssertionFailStmtRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    assert (1) else fork v = 1; join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            3, "9.3.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements and a fork is one of them. They are kept in RsProd::code_stmts,
// reached through Stmt::rs_productions and through no other member of Stmt.
TEST(ParallelBlockElaboration,
     ForkJoinNoneInARandsequenceCodeBlockRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    randsequence(main)\n"
      "      main : { fork v = 1; join_none };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it gets its own
// case: the production `alt` below holds a null statement, which leaves the
// weight block as the only place the fork can stand.
TEST(ParallelBlockElaboration,
     ForkJoinNoneInARandsequenceWeightCodeBlockRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { fork v = 1; join_none };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

}  // namespace
