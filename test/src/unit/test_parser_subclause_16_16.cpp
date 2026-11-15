#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ClockResolutionParse, ClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      $fell(c) |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockPropertyWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      @(posedge clk) a |=> b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a property declared in a clocking block may not "
                            "specify an explicit clocking event",
                            4, "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithExplicitClockIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic b, c, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) b ##1 c;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sequence declared in a clocking block may not "
                            "specify an explicit clocking event",
                            4, "16.16"));
}

TEST(ClockResolutionParse,
     ExplicitClockLegalOnDeclarationOutsideClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  property p1;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, DefaultClockingBlockPropertyWithoutClockIsLegal) {
  auto r = Parse(
      "module m;\n"
      "  logic c, clk;\n"
      "  default clocking pc @(posedge clk);\n"
      "    property p3;\n"
      "      $fell(c) |=> c;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockResolutionParse, ClockingBlockMulticlockedPropertyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p1;\n"
      "      a |=> @(negedge clk) b;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked property is not allowed in a clocking block", 4,
      "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockMulticlockedSequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked sequence is not allowed in a clocking block", 4,
      "16.16"));
}

TEST(ClockResolutionParse, ClockingBlockSequenceWithTwoClocksIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s1;\n"
      "      @(posedge clk) a ##1 @(negedge clk) b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a multiclocked sequence is not allowed in a clocking block", 4,
      "16.16"));
}

const ModuleItem* NamedSequence(const ParseResult& r, std::string_view name) {
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == name) {
      return item;
    }
  }
  return nullptr;
}

TEST(ClockResolutionParse, ASequenceKeepsItsLeadingClockOverANestedGroup) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, e, clk;\n"
      "  sequence s;\n"
      "    @(posedge clk) ((a ##5 b) and (c ##8 d)) ##0 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  EXPECT_EQ(s->seq_clock[0].edge, Edge::kPosedge);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->text, "clk");
  ASSERT_EQ(s->seq_linear.operands.size(), 2u);
  const PropertyExprNode* group = s->seq_linear.operands[0]->property_actual;
  ASSERT_NE(group, nullptr);
  EXPECT_EQ(group->kind, PropertyExprNode::Kind::kSequence);
  ASSERT_NE(group->sequence, nullptr);
  EXPECT_EQ(group->sequence->seq_linear.conjuncts.size(), 1u);
}

TEST(ClockResolutionParse, ASequenceWithoutALeadingClockRecordsNone) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, e, clk;\n"
      "  sequence s;\n"
      "    ((a ##[1:6] b) and (c ##[1:9] d)) ##0 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->seq_clock.empty());
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

TEST(ClockResolutionParse, ASequenceKeepsABareNamedLeadingClock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  event e;\n"
      "  sequence s;\n"
      "    @e a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  EXPECT_EQ(s->seq_clock[0].edge, Edge::kNone);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->text, "e");
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

TEST(ClockResolutionParse, ABareNamedLeadingClockEndsAtTheName) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  event e;\n"
      "  sequence s;\n"
      "    @e (a) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = NamedSequence(r, "s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_clock.size(), 1u);
  ASSERT_NE(s->seq_clock[0].signal, nullptr);
  EXPECT_EQ(s->seq_clock[0].signal->kind, ExprKind::kIdentifier);
  EXPECT_EQ(s->seq_clock[0].signal->text, "e");
  EXPECT_EQ(s->seq_linear.operands.size(), 2u);
}

struct BlockPlace {
  const char* open;
  const char* close;
};

constexpr BlockPlace kInModule{"module m;\n", "endmodule\n"};
constexpr BlockPlace kInInterface{"interface i;\n", "endinterface\n"};
constexpr BlockPlace kInProgram{"program p;\n", "endprogram\n"};
constexpr BlockPlace kInChecker{"checker c;\n", "endchecker\n"};
constexpr BlockPlace kInGenerate{"module m; if (1) begin : g\n",
                                 "end endmodule\n"};

constexpr const char* kPlainBlock = "  clocking cb @(posedge clk);\n";
constexpr const char* kDefaultBlock =
    "  default clocking dcb @(posedge clk);\n";

std::string BlockDecl(const BlockPlace& place, const char* block,
                      const char* kind, const std::string& body) {
  return std::string(place.open) + "  logic a, b, en, rst, clk;\n" + block +
         "    " + kind + " d;\n      " + body + ";\n    end" + kind +
         "\n  endclocking\n" + place.close;
}

std::string ExplicitEventMessage(const char* kind) {
  return std::string("a ") + kind +
         " declared in a clocking block may not specify an explicit "
         "clocking event";
}

void ExpectExplicitEventReported(const BlockPlace& place, const char* block,
                                 const char* kind, const std::string& body) {
  auto r = Parse(BlockDecl(place, block, kind, body));
  ASSERT_NE(r.cu, nullptr) << body;
  EXPECT_TRUE(ReportedError(r.diags, ExplicitEventMessage(kind), 4, "16.16"))
      << place.open << body;
}

void ExpectAccepted(const BlockPlace& place, const char* block,
                    const char* kind, const std::string& body) {
  auto r = Parse(BlockDecl(place, block, kind, body));
  ASSERT_NE(r.cu, nullptr) << body;
  EXPECT_FALSE(r.has_errors) << place.open << body;
}

TEST(ClockResolutionParse, AnEventOtherThanTheBlocksIsRejected) {
  ExpectExplicitEventReported(kInModule, kPlainBlock, "property",
                              "@(negedge clk) a |=> b");
  ExpectExplicitEventReported(kInModule, kPlainBlock, "sequence",
                              "@(negedge clk) a ##1 b");
}

TEST(ClockResolutionParse, ABareNamedEventIsRejected) {
  auto r = Parse(
      "module m; event e;\n"
      "  logic a, b, clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    property d;\n"
      "      @e a;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, ExplicitEventMessage("property"), 4, "16.16"));
  ExpectExplicitEventReported(kInModule, kPlainBlock, "sequence",
                              "@clk a ##1 b");
}

TEST(ClockResolutionParse, EachEventExpressionFormIsRejected) {
  for (const char* body : {"@(edge clk) a", "@(posedge clk iff en) a",
                           "@(posedge clk or negedge rst) a"}) {
    ExpectExplicitEventReported(kInModule, kPlainBlock, "property", body);
  }
}

TEST(ClockResolutionParse, ALeadingEventBeforeDisableIffIsRejected) {
  ExpectExplicitEventReported(kInModule, kPlainBlock, "property",
                              "@(posedge clk) disable iff (rst) a |=> b");
}

TEST(ClockResolutionParse, DisableIffWithoutAnEventIsAccepted) {
  ExpectAccepted(kInModule, kPlainBlock, "property",
                 "disable iff (rst) a |=> b");
}

TEST(ClockResolutionParse,
     DISABLED_ANonLeadingEventIdenticalToTheBlocksIsRejected) {
  ExpectExplicitEventReported(kInModule, kPlainBlock, "property",
                              "a |=> @(posedge clk) b");
  ExpectExplicitEventReported(kInModule, kPlainBlock, "sequence",
                              "a ##1 @(posedge clk) b");
}

TEST(ClockResolutionParse, DISABLED_AnEventUnderAPropertyOperatorIsRejected) {
  for (const char* body : {"not @(posedge clk) a", "if (a) @(posedge clk) b",
                           "a and @(posedge clk) b"}) {
    ExpectExplicitEventReported(kInModule, kPlainBlock, "property", body);
  }
}

TEST(ClockResolutionParse, DISABLED_AParenthesisedLeadingEventIsRejected) {
  ExpectExplicitEventReported(kInModule, kPlainBlock, "property",
                              "(@(posedge clk) a)");
}

TEST(ClockResolutionParse, AnExplicitEventInEachPlacesBlockIsRejected) {
  for (const BlockPlace* place :
       {&kInModule, &kInInterface, &kInProgram, &kInChecker, &kInGenerate}) {
    const char* block = place == &kInModule ? kDefaultBlock : kPlainBlock;
    ExpectExplicitEventReported(*place, block, "property",
                                "@(posedge clk) a |=> b");
    ExpectExplicitEventReported(*place, block, "sequence",
                                "@(posedge clk) a ##1 b");
  }
}

TEST(ClockResolutionParse, NoEventInEachPlacesBlockIsAccepted) {
  for (const BlockPlace* place :
       {&kInModule, &kInInterface, &kInProgram, &kInChecker, &kInGenerate}) {
    const char* block = place == &kInModule ? kDefaultBlock : kPlainBlock;
    ExpectAccepted(*place, block, "property", "a |=> b");
    ExpectAccepted(*place, block, "sequence", "a ##1 b");
  }
}

}  // namespace
