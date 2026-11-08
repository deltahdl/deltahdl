#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/typed_sequence_formal.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(TypedSequenceFormal, AllowedTypeKindsIncludeUntypedSequenceEventIntegral) {
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kUntyped));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kSequence));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kEvent));
  EXPECT_TRUE(
      IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kIntegralOrUserType));
}

TEST(TypedSequenceFormal, ForbiddenTypeKindRejected) {
  EXPECT_FALSE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kForbidden));
}

TEST(TypedSequenceFormal, SequenceTypedRefLegalPlaces) {
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kSequenceExprPosition));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kTriggeredMethodOperand));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kMatchedMethodOperand));
  EXPECT_FALSE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kOtherPosition));
}

TEST(TypedSequenceFormal, EventTypedRefRequiresEventExpressionPosition) {
  EXPECT_TRUE(IsEventTypedFormalRefLegal(true));
  EXPECT_FALSE(IsEventTypedFormalRefLegal(false));
}

TEST(TypedSequenceFormal, SequenceTypedFormalForbiddenAsGotoOperand) {
  EXPECT_FALSE(IsSequenceTypedFormalAllowedAsGotoOperand());
}

TEST(TypedSequenceFormal, TypedFormalLvalueInMatchItemOnlyForLocalVar) {
  EXPECT_FALSE(IsTypedFormalAllowedAsMatchItemLvalue(false));
  EXPECT_TRUE(IsTypedFormalAllowedAsMatchItemLvalue(true));
}

TEST(TypedSequenceFormal, DelayAndRepetitionIndexTypeRestricted) {
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kShortint));
  EXPECT_TRUE(
      IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType::kInt));
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kLongint));
  EXPECT_FALSE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kOtherIntegral));
}

TEST(TypedSequenceFormal, SubstitutionModePicksLvalueVsCast) {
  EXPECT_EQ(TypedFormalSubstitution(true),
            TypedFormalSubstitutionMode::kAssignBackAfterUpdate);
  EXPECT_EQ(TypedFormalSubstitution(false),
            TypedFormalSubstitutionMode::kCastBeforeSubstitution);
}

TEST(TypedSequenceFormal, UntypedKeywordRequiredAfterTypedFormal) {
  EXPECT_TRUE(IsUntypedKeywordRequired(true, true));
  EXPECT_FALSE(IsUntypedKeywordRequired(false, true));
  EXPECT_FALSE(IsUntypedKeywordRequired(true, false));
}

TEST(TypedSequenceFormal, EventTypedFormalRejectsEdgeIdentifierActual) {
  EXPECT_FALSE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(true, true));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(true, false));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(false, true));
}

std::string EventText(const EventExpr& ev) {
  std::string edge;
  if (ev.edge == Edge::kPosedge) edge = "posedge ";
  if (ev.edge == Edge::kNegedge) edge = "negedge ";
  return edge + std::string(ev.signal != nullptr ? ev.signal->text : "");
}

std::vector<std::string> AssertionWakeEvents(const std::string& src) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(src, f, "t");
  std::vector<std::string> events;
  if (design == nullptr || f.has_errors || design->top_modules.empty()) {
    return events;
  }
  for (const RtlirProcess& p : design->top_modules[0]->processes) {
    if (p.kind != RtlirProcessKind::kAlwaysFF) continue;
    for (const EventExpr& ev : p.sensitivity) events.push_back(EventText(ev));
  }
  return events;
}

TEST(TypedSequenceFormal, AnInstancesClockTakesTheEventFormalsActual) {
  EXPECT_EQ(
      AssertionWakeEvents(
          "module t;\n"
          "  logic clk, a;\n"
          "  sequence s_ev(event ev, untyped x); @(ev) x ##2 !x; endsequence\n"
          "  cover property (s_ev(posedge clk, a));\n"
          "endmodule\n"),
      std::vector<std::string>{"posedge clk"});
}

TEST(TypedSequenceFormal, AnInstancesClockTakesTheSignalFormalsActual) {
  EXPECT_EQ(
      AssertionWakeEvents(
          "module t;\n"
          "  logic clk, a;\n"
          "  sequence s_ev2(reg sig, x); @(posedge sig) x ##2 !x; endsequence\n"
          "  cover property (s_ev2(clk, a));\n"
          "endmodule\n"),
      std::vector<std::string>{"posedge clk"});
}

TEST(TypedSequenceFormal, AListBoundToTheBooleanFormalTakesTheTree) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  function void note; endfunction\n"
      "  property p(q, r); @(posedge clk) q; endproperty\n"
      "  property w(q); @(posedge clk) a; endproperty\n"
      "  property v(q); @(posedge clk) q && b; endproperty\n"
      "  property t(q); @(posedge clk) q |-> b; endproperty\n"
      "  assert property (p((a, note), c));\n"
      "  assert property (p(c, (a, note)));\n"
      "  assert property (p(b, c));\n"
      "  assert property (p(, c));\n"
      "  assert property (w((a, note)));\n"
      "  assert property (v((a, note)));\n"
      "  assert property (t(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<const ModuleItem*> decls;
  std::vector<const Expr*> instances;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) decls.push_back(item);
    if (item->kind == ModuleItemKind::kAssertProperty) {
      instances.push_back(item->assert_expr);
    }
  }
  ASSERT_EQ(decls.size(), 4u);
  ASSERT_EQ(instances.size(), 7u);
  const std::vector<const ModuleItem*> kDeclOf = {
      decls[0], decls[0], decls[0], decls[0], decls[1], decls[2], decls[3]};
  const std::vector<bool> kSubstituted = {false, true, true, true,
                                          true,  true, false};
  for (size_t i = 0; i < instances.size(); ++i) {
    ASSERT_NE(instances[i], nullptr) << "instance " << i;
    EXPECT_EQ(TakesBooleanSubstitution(instances[i], kDeclOf[i]),
              kSubstituted[i])
        << "instance " << i;
  }
}

std::ptrdiff_t ReportsOnLine(const std::vector<Diagnostic>& diags,
                             uint32_t line, std::string_view message) {
  return std::ranges::count_if(diags, [&](const Diagnostic& d) {
    return d.severity == DiagSeverity::kError && d.loc.line == line &&
           d.subclause == "16.8.1" &&
           d.message.find(message) != std::string::npos;
  });
}

TEST(TypedSequenceFormal, ATypedFormalAssignedInAMatchItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(int x);\n"
      "    (a, x = 1) ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(bit [3:0] y);\n"
      "    (a, y++) ##1 b;\n"
      "  endsequence\n"
      "  sequence s3(local inout int z);\n"
      "    (a, z += 1);\n"
      "  endsequence\n"
      "  sequence s4(w);\n"
      "    (a, w = 1);\n"
      "  endsequence\n"
      "  property p(int x);\n"
      "    @(posedge clk) (a, x = 1) |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 's1' is "
                            "assigned in a sequence match item",
                            4, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'y' of 's2' is "
                            "assigned in a sequence match item",
                            7, "16.8.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "'z' of 's3'", 10, "16.8.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "'w' of 's4'", 13, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 'p' is "
                            "assigned in a sequence match item",
                            16, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'x' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'y' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 16, "'x' of 'p'"), 1);
}

TEST(TypedSequenceFormal, ABoundOfAnotherTypeIsReported) {
  const char* const kReport =
      "bounds a cycle delay or a repetition but is of a type other than "
      "shortint, int or longint";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(bit [3:0] d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  sequence s2(byte n);\n"
      "    a ##1 b[*n];\n"
      "  endsequence\n"
      "  sequence s3(logic [7:0] g);\n"
      "    a ##1 b[->g];\n"
      "  endsequence\n"
      "  sequence s4(shortint d1, int d2, longint d3);\n"
      "    a ##d1 b ##[d2:d3] a[=d1];\n"
      "  endsequence\n"
      "  sequence s5(d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  sequence s6(bit [3:0] v, int k);\n"
      "    v[0] ##k b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'd' of 's1' ") + kReport, 4, "16.8.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'n' of 's2' ") + kReport, 7, "16.8.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'g' of 's3' ") + kReport, 10, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 16, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 19, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'d' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'n' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 10, "'g' of 's3'"), 1);
}

TEST(TypedSequenceFormal, ASequenceFormalAsAGotoOperandIsReported) {
  const char* const kReport =
      "is of type sequence and is the operand of a "
      "goto repetition";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(sequence q);\n"
      "    q[->1] ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(sequence q);\n"
      "    q ##1 b[->1];\n"
      "  endsequence\n"
      "  sequence s3(q);\n"
      "    q[->1] ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'q' of 's1' ") + kReport, 4, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'q' of 's1'"), 1);
}

TEST(TypedSequenceFormal, AFormalInsideANestedGroupIsHeldToTheRules) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(bit [3:0] d);\n"
      "    a ##1 (a ##d b or b) ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(int x);\n"
      "    a ##1 ((a, x = 1) or b);\n"
      "  endsequence\n"
      "  sequence s3(sequence q);\n"
      "    a ##1 (b or q[->1]);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal argument 'd' of 's1' bounds a cycle "
                            "delay or a repetition",
                            4, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 's2' is "
                            "assigned in a sequence match item",
                            7, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal argument 'q' of 's3' is of type "
                            "sequence and is the operand of a goto repetition",
                            10, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'d' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'x' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 10, "'q' of 's3'"), 1);
}

}  // namespace
