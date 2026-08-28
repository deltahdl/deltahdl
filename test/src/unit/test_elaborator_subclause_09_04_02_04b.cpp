// §9.4.2.4 "Sequence events": the statement links a sequence instance used as
// an event control can be written in. The cases in
// test_elaborator_subclause_09_04_02_04a.cpp write the event control where such
// a control is normally written -- at the top of a task body -- and each of the
// five below writes it in one of the seven links
// WalkStmtsForSequenceEvents in
// src/elaborator/elaborator_validate_assertion_actions.cpp did not descend
// before it was handed the list ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. An `@(s(a, b))` in any
// of them was neither marked a sequence event nor argument-counted, so the
// restriction below went unenforced there.
//
// The rule is §9.4.2.4's: an argument to a sequence used in an event control
// shall be static, so a local of an automatic task passed as one is an error.
// The issue tabling this walk cited §16.13, which is "Multiclock support" and
// states no rule about a statement link; the emission site passes
// Subclause("9.4.2.4"), which is what these cases name.
//
// A.6.8 admits in a for_initialization only a list_of_variable_assignments or a
// for_variable_declaration, and in a for_step_assignment only an
// operator_assignment, an inc_or_dec_expression or a function_subroutine_call.
// A procedural_timing_control_statement is none of those, so no conforming
// source writes an event control in a for header and neither Stmt::for_inits
// nor Stmt::for_steps takes a case.

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork arm
// holds a procedural timing control statement.
TEST(SequenceEventStatementLinks, AutomaticArgInAForkArmErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    fork\n"
      "      @(s(a, b)) $display(\"matched\");\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so either arm of an immediate assertion holds one.
TEST(SequenceEventStatementLinks, AutomaticArgInAnAssertionPassActionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    assert (1'b1) @(s(a, b)) $display(\"matched\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            8, "9.4.2.4"));
}

TEST(SequenceEventStatementLinks, AutomaticArgInAnAssertionFailActionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    assert (1'b1) else @(s(a, b)) $display(\"matched\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            8, "9.4.2.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`. §9.4.2.4 is
// a rule about the source, so it holds whether the weighted draw would select
// the arm or not.
TEST(SequenceEventStatementLinks, AutomaticArgInARandcaseArmErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    randcase\n"
      "      1 : @(s(a, b)) $display(\"matched\");\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds one.
TEST(SequenceEventStatementLinks, AutomaticArgInARandsequenceCodeBlockErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(logic x, logic y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  task automatic t;\n"
      "    logic a, b;\n"
      "    randsequence(main)\n"
      "      main : { @(s(a, b)) $display(\"matched\"); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence event arguments shall not reference "
                            "automatic variables",
                            9, "9.4.2.4"));
}

}  // namespace
