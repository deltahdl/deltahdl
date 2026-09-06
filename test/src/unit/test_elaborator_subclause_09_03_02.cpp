#include <cstddef>
#include <string_view>

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

// The three cases below are §9.3.2 cases about a report withheld.
// CheckNoReturnInFork in src/elaborator/elaborator_validate_funcbody.cpp is the
// walk that finds the return §9.3.2 forbids, and it now takes its
// child-statement links from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, which reaches
// Stmt::rs_productions. §18.17.6 "Aborting productions—break and return" says
// "The return statement aborts the generation of the current production", so a
// return written in a randsequence production code block is not the enclosing
// subroutine's return and "A return statement within the context of a fork-join
// block is illegal" is not the rule that governs it. Take
// CheckNoReturnInFork::in_production_code_block away and each source below is
// rejected.
//
// Stmt::for_inits and Stmt::for_steps are newly reached too and get no case:
// A.6.8 admits only a list_of_variable_assignments or a
// for_variable_declaration in a for_initialization and only an
// operator_assignment, an inc_or_dec_expression or a function_subroutine_call
// in a for_step, and a jump_statement is none of those.

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }` and an rs_prod may be one, whose statements the parser keeps in
// RsProd::code_stmts.
TEST(ParallelBlockElaboration,
     ReturnInARandsequenceCodeBlockInAForkIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : { return; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, kept in
// RsRule::weight_code rather than in RsProd::code_stmts, so it is a second
// statement position under Stmt::rs_productions and gets its own case.
TEST(ParallelBlockElaboration,
     ReturnInARandsequenceWeightCodeBlockInAForkIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : alt := 5 { return; };\n"
      "        alt : { ; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The fork below the production rather than above it. §18.17.6 states what the
// return does without qualifying it by what stands between the return and the
// production, so the return here still aborts the production and is still not
// the subroutine's return, however many processes the fork spawns in between.
// CheckNoReturnInFork keeps its §18.17.6 term set through a fork for that
// reason, which is the same reading JumpScope::in_production_code_block in
// src/elaborator/elaborator_validate_jump_statements.cpp records for §12.8.
TEST(ParallelBlockElaboration,
     ReturnInAForkInARandsequenceCodeBlockIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randsequence(main)\n"
      "      main : { fork return; join_none };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// How many recorded diagnostics carry `needle` under §9.3.2. The cases below
// count rather than calling ReportedError, which answers whether a report was
// made and cannot say it was made once; counting one named report rather than
// the run's total keeps each case about the rule it names.
size_t CountReports(const ElabFixture& f, std::string_view needle) {
  size_t n = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.subclause == "9.3.2" && d.message.find(needle) != std::string::npos) {
      ++n;
    }
  }
  return n;
}

// §9.3.2: "A return statement within the context of a fork-join block is
// illegal and shall result in a compilation error." One return inside two
// fork-join blocks is one return in that context, so it is one error.
//
// It was two. CheckNoReturnInFork descends every child-statement link,
// Stmt::fork_stmts among them, so an entry made at the outer fork already
// reaches the return under the inner one; the enclosing walk then entered again
// at the inner fork. Three nested forks gave three reports, and a count of
// errors stood one higher than the number of things wrong with the source.
TEST(ParallelBlockElaboration, ReturnInNestedForksIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      fork\n"
      "        return;\n"
      "      join\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountReports(f,
                         "return statement is not allowed inside a "
                         "fork-join block"),
            1u);
}

// §9.3.2's other rule, reached by its own walk and duplicated the same way: a
// ref argument used inside two fork-join_none blocks was reported once per
// enclosing fork. CheckRefArgsInForkBlocks handed the whole subtree to
// CheckStmtForRefArgs at each of them.
TEST(ParallelBlockElaboration, RefArgInNestedForkJoinNoneIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(ref int v);\n"
      "    fork\n"
      "      fork\n"
      "        v = 1;\n"
      "      join_none\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountReports(f,
                         "ref argument 'v' cannot be used inside a "
                         "fork-join_any or fork-join_none block"),
            1u);
}

}  // namespace
