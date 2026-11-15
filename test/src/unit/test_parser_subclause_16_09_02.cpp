#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, ConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, ARepetitionAloneIsASequentialProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*0:2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* item = nullptr;
  for (auto* candidate : r.cu->modules[0]->items) {
    if (candidate->kind == ModuleItemKind::kAssertProperty) item = candidate;
  }
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  ASSERT_NE(item->body->assert_sequence, nullptr);
  const SeqLinearBody& body = item->body->assert_sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 1u);
  EXPECT_EQ(body.repetitions[0].kind, SeqRepetition::Kind::kConsecutive);
  EXPECT_EQ(body.repetitions[0].min, 0u);
  EXPECT_EQ(body.repetitions[0].max, 2u);
}

TEST(AssertionSemanticsParsing, GotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonconsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[=2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceRepetitionParsing, AGroupRepeatedByARangeIsOneNestedOperand) {
  auto r = Parse(
      "module m;\n"
      "  localparam int N = 2;\n"
      "  sequence s_range; (a ##1 b)[*1:2] ##1 c; endsequence\n"
      "  sequence s_plus; (a ##1 b)[+] ##1 c; endsequence\n"
      "  sequence s_zero; (a ##1 b)[*0] ##1 c; endsequence\n"
      "  sequence s_param; (a ##1 b)[*N] ##1 c; endsequence\n"
      "  sequence s_exact; (a ##1 b)[*2] ##1 c; endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  struct Expected {
    std::string_view name;
    uint32_t min;
    uint32_t max;
    bool count_expr;
  };
  for (const Expected& want :
       {Expected{"s_range", 1, 2, false},
        Expected{"s_plus", 1, SeqCycleDelay::kUnbounded, false},
        Expected{"s_zero", 0, 0, false}, Expected{"s_param", 0, 0, true}}) {
    SCOPED_TRACE(want.name);
    const ModuleItem* seq = FindItemByName(r.cu->modules[0]->items, want.name);
    ASSERT_NE(seq, nullptr);
    const SeqLinearBody& body = seq->seq_linear;
    ASSERT_EQ(body.operands.size(), 2u);
    const SeqRepetition& rep = body.repetitions[0];
    EXPECT_EQ(rep.kind, SeqRepetition::Kind::kConsecutive);
    EXPECT_EQ(rep.max_expr != nullptr, want.count_expr);
    if (!want.count_expr) {
      EXPECT_EQ(rep.min, want.min);
      EXPECT_EQ(rep.max, want.max);
    }
    const PropertyExprNode* group = body.operands[0]->property_actual;
    ASSERT_NE(group, nullptr);
    ASSERT_NE(group->sequence, nullptr);
    EXPECT_EQ(group->sequence->seq_linear.operands.size(), 2u);
    EXPECT_EQ(body.operands[1]->text, "c");
  }
  const ModuleItem* exact = FindItemByName(r.cu->modules[0]->items, "s_exact");
  ASSERT_NE(exact, nullptr);
  EXPECT_EQ(exact->seq_linear.operands.size(), 5u);
}

TEST(SequenceRepetitionParsing, ARepeatedGroupsMatchItemsEndEachIteration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    (a ##1 b, x = 1)[*1:2] ##1 c;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* seq = FindItemByName(r.cu->modules[0]->items, "s");
  ASSERT_NE(seq, nullptr);
  const SeqLinearBody& body = seq->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  EXPECT_TRUE(body.match_items[1].empty());
  const PropertyExprNode* group = body.operands[0]->property_actual;
  ASSERT_NE(group, nullptr);
  ASSERT_NE(group->sequence, nullptr);
  const SeqLinearBody& inner = group->sequence->seq_linear;
  ASSERT_EQ(inner.operands.size(), 2u);
  EXPECT_TRUE(inner.match_items[0].empty());
  ASSERT_EQ(inner.match_items[1].size(), 1u);
  EXPECT_EQ(inner.match_items[1][0].lvar, "x");
}

constexpr const char* kUnboundedPlaces[] = {
    "module m;\n  logic clk, a, b, c;\n"
    "  sequence s; a ##1 b%s ##1 c; endsequence\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  property p; a ##1 b%s ##1 c; endproperty\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  assert property (@(posedge clk) a ##1 b%s ##1 c);\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n  always @(posedge clk)\n"
    "    assert property (@(posedge clk) a ##1 b%s ##1 c);\nendmodule\n",
};

std::string Placed(const char* place, const std::string& repetition) {
  std::string src = place;
  return src.replace(src.find("%s"), 2, repetition);
}

TEST(SequenceRepetitionParsing, GotoAndNonconsecutiveTakeAnUnboundedMaximum) {
  for (const char* place : kUnboundedPlaces) {
    for (const char* repetition : {"[->2:$]", "[=2:$]"}) {
      std::string src = Placed(place, repetition);
      auto r = Parse(src);
      EXPECT_FALSE(r.has_errors) << src;
    }
  }
  std::string second = Placed(kUnboundedPlaces[0], "[=2:$]");
  second.replace(second.find("module m"), 8, "module n");
  auto r = Parse(Placed(kUnboundedPlaces[0], "[->2:$]") + second);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  const SeqRepetition::Kind kKinds[] = {SeqRepetition::Kind::kGoto,
                                        SeqRepetition::Kind::kNonconsecutive};
  for (size_t i = 0; i < 2; ++i) {
    const ModuleItem* seq = FindItemByName(r.cu->modules[i]->items, "s");
    ASSERT_NE(seq, nullptr);
    const SeqRepetition& rep = seq->seq_linear.repetitions[1];
    EXPECT_EQ(rep.kind, kKinds[i]);
    EXPECT_EQ(rep.min, 2u);
    EXPECT_EQ(rep.max, SeqCycleDelay::kUnbounded);
  }
}

constexpr const char* kUnadmitted = "not one the grammar admits";

void ExpectUnadmitted(const std::string& src, const std::string& form) {
  auto r = Parse(src);
  EXPECT_TRUE(
      ReportedError(r.diags, kUnadmitted, LineHolding(src, form), "A.2.10"))
      << src;
}

void ExpectAdmitted(const std::string& src) {
  auto r = Parse(src);
  EXPECT_FALSE(r.has_errors) << src;
}

constexpr const char* kCountlessPlaces[] = {
    "module m;\n  logic clk, a, b, c;\n"
    "  sequence s;\n    a ##1 b%s ##1 c;\n  endsequence\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  property p;\n    a ##1 b%s ##1 c;\n  endproperty\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  assert property (@(posedge clk)\n    a ##1 b%s ##1 c);\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n  always @(posedge clk)\n"
    "    assert property (@(posedge clk)\n    a ##1 b%s ##1 c);\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  cover sequence (@(posedge clk)\n    a ##1 b%s ##1 c);\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n  initial\n"
    "    expect (@(posedge clk)\n    a ##1 b%s ##1 c);\nendmodule\n",
    "module m;\n  logic clk, a, b, c;\n"
    "  sequence s(x); x ##1 c; endsequence\n"
    "  assert property (@(posedge clk)\n    s(b%s));\nendmodule\n",
    "package pk;\n  sequence s(y, z);\n    y%s ##1 z;\n  endsequence\n"
    "endpackage\n",
    "interface i(input logic y, z);\n  sequence s;\n    y%s ##1 z;\n"
    "  endsequence\nendinterface\n",
    "program p(input logic y, z);\n  sequence s;\n    y%s ##1 z;\n"
    "  endsequence\nendprogram\n",
    "checker ck(logic y, logic z);\n  sequence s;\n    y%s ##1 z;\n"
    "  endsequence\nendchecker\n",
    "module m;\n  logic y, z;\n  if (1) begin : g\n  sequence s;\n"
    "    y%s ##1 z;\n  endsequence\n  end\nendmodule\n",
    "module m;\n  logic clk, y, z;\n  clocking cb @(posedge clk);\n"
    "  sequence s;\n    y%s ##1 z;\n  endsequence\n  endclocking\n"
    "endmodule\n",
    "sequence s(y, z);\n  y%s ##1 z;\nendsequence\n",
};

TEST(SequenceRepetitionParsing, GotoAndNonconsecutiveWithoutACountAreReported) {
  for (const char* place : kCountlessPlaces) {
    for (const char* repetition : {"[->]", "[=]"}) {
      ExpectUnadmitted(Placed(place, repetition), repetition);
    }
    for (const char* repetition : {"[*]", "[->1]", "[=1]"}) {
      ExpectAdmitted(Placed(place, repetition));
    }
  }
}

TEST(SequenceRepetitionParsing, PlusWithACountIsReportedInADeclaration) {
  for (const char* place : {kCountlessPlaces[0], kCountlessPlaces[1]}) {
    ExpectUnadmitted(Placed(place, "[+2]"), "[+2]");
    ExpectAdmitted(Placed(place, "[+]"));
    ExpectAdmitted(Placed(place, "[*2]"));
  }
}

}  // namespace
