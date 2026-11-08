#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

using namespace delta;

namespace {

TEST(TypedSequenceFormalSyntax, UntypedKeywordAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x, untyped y);\n"
              "    x ##1 y;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, SequenceTypedFormalAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence inner;\n"
              "    1'b1 ##1 1'b1;\n"
              "  endsequence\n"
              "  sequence s(sequence q);\n"
              "    q ##1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, EventTypedFormalAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(event ev);\n"
              "    @(ev) 1'b1 ##1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, IntegralTypedFormalAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(bit x, byte y);\n"
              "    x ##1 y;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, BareFormalAfterTypedInheritsType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence d(max, shortint delay1, delay2, min);\n"
              "    1'b1 ##delay1 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, UserDefinedTypeTypedFormalAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef logic [3:0] nibble_t;\n"
              "  sequence s(nibble_t x);\n"
              "    x[0] ##1 x[1];\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, EventFormalReferencedAsBooleanRejected) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_ev(event ev, event x);\n"
      "    @(ev) x ##2 !x;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "formal argument 'x' of type event is referenced "
                            "where no event expression may be written",
                            3, "16.8.1"));
}

TEST(TypedSequenceFormalSyntax, EventTypeCarriedToFollowingFormalRejected) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_ev(event ev,\n"
      "                x);\n"
      "    @(ev) x ##2 !x;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "formal argument 'x' of type event is referenced "
                            "where no event expression may be written",
                            4, "16.8.1"));
}

TEST(TypedSequenceFormalSyntax, UntypedFormalAfterEventFormalAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s_ev(event ev, untyped x);\n"
              "    @(ev) x ##2 !x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, EventFormalAsBareClockingEventAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a;\n"
              "  sequence s(event ev);\n"
              "    @ev a ##1 !a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(TypedSequenceFormalSyntax, EventFormalPassedWholeToAnInstanceAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a;\n"
              "  sequence inner(event e);\n"
              "    @(e) a;\n"
              "  endsequence\n"
              "  sequence s(event ev);\n"
              "    inner(ev) ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceActualParsing, AListOfNamesKeepsItsSequenceReading) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  function void note; endfunction\n"
      "  property p(q);\n"
      "    @(posedge clk) q |-> b;\n"
      "  endproperty\n"
      "  assert property (p((a, note)));\n"
      "  assert property (p((a, note) ##1 b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<const Expr*> actuals;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kAssertProperty) continue;
    ASSERT_NE(item->assert_expr, nullptr);
    ASSERT_EQ(item->assert_expr->args.size(), 1u);
    actuals.push_back(item->assert_expr->args[0]);
  }
  ASSERT_EQ(actuals.size(), 2u);
  const Expr* listed = actuals[0];
  ASSERT_NE(listed, nullptr);
  EXPECT_TRUE(IsEventActual(listed));
  ASSERT_NE(listed->sequence_reading, nullptr);
  const ModuleItem* sequence = listed->sequence_reading->sequence;
  ASSERT_NE(sequence, nullptr);
  const SeqLinearBody& body = sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 1u);
  ASSERT_NE(body.operands[0], nullptr);
  EXPECT_EQ(body.operands[0]->text, "a");
  ASSERT_EQ(body.match_items[0].size(), 1u);
  ASSERT_NE(body.match_items[0][0].call, nullptr);
  EXPECT_EQ(body.match_items[0][0].call->callee, "note");
  ASSERT_NE(actuals[1], nullptr);
  EXPECT_EQ(actuals[1]->text, "<property_actual>");
  EXPECT_EQ(actuals[1]->sequence_reading, nullptr);
}

}  // namespace
