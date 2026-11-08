#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const RtlirProcess* AssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

Expr* GlobalClockRef(ElabFixture& f) {
  auto* e = f.arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = "$global_clock";
  return e;
}

Expr* Ident(ElabFixture& f, std::string_view name) {
  auto* e = f.arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

TEST(AssertionClockGlobalClock,
     GlobalClockLeadingEventBecomesTheGlobalClockingEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, clk;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  assert property (@$global_clock a);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirProcess* p = AssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kPosedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
}

TEST(AssertionClockGlobalClock,
     GlobalClockTakesTheDeclaredEdgeRatherThanADefaultOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, clk;\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "  assert property (@$global_clock a);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirProcess* p = AssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
}

TEST(AssertionClockGlobalClock, SubstitutionLeavesAnOrdinaryLeadingEventAlone) {
  ElabFixture f;
  std::vector<EventExpr> sensitivity(1);
  sensitivity[0].edge = Edge::kPosedge;
  sensitivity[0].signal = Ident(f, "sample");

  std::vector<EventExpr> global_event(1);
  global_event[0].edge = Edge::kNegedge;
  global_event[0].signal = Ident(f, "gclk");

  EXPECT_FALSE(SubstituteGlobalClockLeadingEvent(sensitivity, global_event));
  ASSERT_EQ(sensitivity.size(), 1u);
  EXPECT_EQ(sensitivity[0].edge, Edge::kPosedge);
  ASSERT_NE(sensitivity[0].signal, nullptr);
  EXPECT_EQ(sensitivity[0].signal->text, "sample");
}

TEST(AssertionClockGlobalClock,
     SubstitutionWithoutAGlobalClockingEventLeavesTheLeadingEventAsItStands) {
  ElabFixture f;
  std::vector<EventExpr> sensitivity(1);
  sensitivity[0].edge = Edge::kNegedge;
  sensitivity[0].signal = GlobalClockRef(f);

  std::vector<EventExpr> global_event;

  EXPECT_FALSE(SubstituteGlobalClockLeadingEvent(sensitivity, global_event));
  ASSERT_EQ(sensitivity.size(), 1u);
  EXPECT_EQ(sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(sensitivity[0].signal, nullptr);
  EXPECT_TRUE(IsGlobalClockLeadingEvent(sensitivity));
}

TEST(AssertionClockGlobalClock,
     SubstitutionCarriesTheGateOntoTheGlobalClockingEvent) {
  ElabFixture f;
  Expr* gate = Ident(f, "en");
  std::vector<EventExpr> sensitivity(1);
  sensitivity[0].edge = Edge::kNone;
  sensitivity[0].signal = GlobalClockRef(f);
  sensitivity[0].iff_condition = gate;

  std::vector<EventExpr> global_event(1);
  global_event[0].edge = Edge::kNegedge;
  global_event[0].signal = Ident(f, "gclk");

  EXPECT_TRUE(SubstituteGlobalClockLeadingEvent(sensitivity, global_event));
  ASSERT_EQ(sensitivity.size(), 1u);
  EXPECT_EQ(sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(sensitivity[0].signal, nullptr);
  EXPECT_EQ(sensitivity[0].signal->text, "gclk");
  EXPECT_EQ(sensitivity[0].iff_condition, gate);
}

TEST(AssertionClockGlobalClock,
     SubstitutionKeepsTheGlobalClockingEventsOwnGate) {
  ElabFixture f;
  std::vector<EventExpr> sensitivity(1);
  sensitivity[0].edge = Edge::kNone;
  sensitivity[0].signal = GlobalClockRef(f);

  Expr* ready = Ident(f, "ready");
  std::vector<EventExpr> global_event(1);
  global_event[0].edge = Edge::kPosedge;
  global_event[0].signal = Ident(f, "gclk");
  global_event[0].iff_condition = ready;

  EXPECT_TRUE(SubstituteGlobalClockLeadingEvent(sensitivity, global_event));
  ASSERT_EQ(sensitivity.size(), 1u);
  EXPECT_EQ(sensitivity[0].edge, Edge::kPosedge);
  ASSERT_NE(sensitivity[0].signal, nullptr);
  EXPECT_EQ(sensitivity[0].signal->text, "gclk");
  EXPECT_EQ(sensitivity[0].iff_condition, ready);
}

}  // namespace
