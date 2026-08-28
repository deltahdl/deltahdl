#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BoundedQueueElaboration, BoundedQueueDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:255]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 256);
}

TEST(BoundedQueueElaboration, BoundOfOneIsValid) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 2);
}

// The rule on the bound's value belongs to §7.10, which states under Syntax
// 7-4 "constant_expression shall evaluate to a positive integer value";
// §7.10.5 states only how a bounded queue behaves once declared, so the report
// names §7.10.
TEST(BoundedQueueElaboration, BoundOfZeroIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:0]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

// The report names §7.10 for the reason given above BoundOfZeroIsError.
TEST(BoundedQueueElaboration, NegativeBoundIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:-1]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

// §7.10, Syntax 7-4: the bound in `[$:N]` "shall evaluate to a positive
// integer value", and the subclause puts no scope on that, so a declaration
// inside a procedural block is held to it as a module item's declaration is.
// The report names §7.10 for the reason given above BoundOfZeroIsError.
TEST(BoundedQueueElaboration, BlockScopedBoundOfZeroIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int q[$:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 3,
                            "7.10"));
}

// §7.10, Syntax 7-4 puts no condition on where the declaration carrying the
// bound stands, so the rule is owed in every position a statement holds a
// statement in. CheckBlockQueueBounds in src/elaborator/queue_dim.cpp had
// written out eight of the thirteen child-statement links Stmt declares; it now
// takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, and the five cases below cover
// one newly reached position each. Stmt::for_steps is the sixth and gets no
// case: A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, none of which declares
// anything.
//
// `stmt` may run to several lines, so the line the report stands at is read
// back out of the source rather than counted. The report names §7.10 for the
// reason given above BoundOfZeroIsError.
void ExpectBlockQueueBoundErrorIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer",
                            LineHolding(src, "int q[$:0];"), "7.10"));
}

// A.6.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. A.6.3's seq_block
// admits a block_item_declaration, which is how the declaration stands inside
// one. This case and the next cover one arm each.
TEST(BoundedQueueElaboration, BoundOfZeroInAnAssertionPassStmt) {
  ExpectBlockQueueBoundErrorIn("assert (ok) begin int q[$:0]; end");
}

TEST(BoundedQueueElaboration, BoundOfZeroInAnAssertionFailStmt) {
  ExpectBlockQueueBoundErrorIn("assert (ok) else begin int q[$:0]; end");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §7.10 is a rule about the declaration, so it holds whether the
// weighted draw would select the item or not.
TEST(BoundedQueueElaboration, BoundOfZeroInARandcaseItem) {
  ExpectBlockQueueBoundErrorIn("randcase 1: begin int q[$:0]; end endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds the declaration
// directly. The parser keeps it in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(BoundedQueueElaboration, BoundOfZeroInARandsequenceCodeBlock) {
  ExpectBlockQueueBoundErrorIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { int q[$:0]; };\n"
      "      endsequence\n"
      "    end");
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, kept in
// RsRule::weight_code rather than in RsProd::code_stmts, so it is a second
// statement position under Stmt::rs_productions and the case above does not
// answer for it.
TEST(BoundedQueueElaboration, BoundOfZeroInARandsequenceWeightCodeBlock) {
  ExpectBlockQueueBoundErrorIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { int q[$:0]; };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
