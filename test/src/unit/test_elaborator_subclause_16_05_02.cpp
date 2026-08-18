#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

// §16.5.2 "Assertion clock": under a `global clocking @clk; endclocking`
// declaration, `assert property(@$global_clock a);` is logically equivalent to
// `assert property(@clk a);`. The equivalence is what these cases are about:
// the assertion is clocked by the event the global clocking declaration names,
// and an implementation that leaves the $global_clock reference standing in the
// sensitivity clocks the assertion on nothing at all.

using namespace delta;

namespace {

// The kAlwaysFF process a static concurrent assertion is lowered to, or nullptr
// when the module holds none. The assertion's clock is that process's
// sensitivity, so this is where the substituted event is read back.
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

// §16.5.2: `assert property(@$global_clock a);` under `global clocking gclk
// @(posedge clk); endclocking` is equivalent to `assert property(@(posedge clk)
// a);`, so the lowered process waits on posedge clk. This fails whenever the
// $global_clock system call is left standing in the sensitivity, because the
// process then names no signal to wait on and the assertion is never evaluated.
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

// §16.5.2: the substituted event is the one the global clocking declaration
// wrote, edge included, so `global clocking gclk @(negedge clk); endclocking`
// clocks the assertion on negedge clk. This fails on an implementation that
// substitutes a posedge of its own choosing rather than the declared event --
// which the posedge case above cannot tell apart from the rule.
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

// §16.5.2: the equivalence is stated for $global_clock alone, so an assertion
// that wrote its own clocking event keeps it. This fails on an implementation
// that rewrites every leading clocking event once a global clocking is in
// scope, which would silence `@(posedge sample) a` onto the global clock. The
// global event offered here is non-empty and names a different signal and a
// different edge, so a rewrite would be visible and `false` cannot be the
// answer to an empty offer.
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

// §16.5.2: the equivalence names the clocking event of a global clocking
// declaration, so with no such event there is nothing to substitute and the
// leading clocking event stands as written. §14.14 reports the $global_clock
// reference that has no global clocking in scope, and leaving the sensitivity
// alone leaves that report the only account of it. This fails on an
// implementation that empties or clears the sensitivity when the offer is
// empty, which would replace the §14.14 report with a clockless process.
TEST(AssertionClockGlobalClock,
     SubstitutionWithoutAGlobalClockingEventLeavesTheLeadingEventAsItStands) {
  ElabFixture f;
  std::vector<EventExpr> sensitivity(1);
  sensitivity[0].edge = Edge::kNegedge;
  sensitivity[0].signal = GlobalClockRef(f);

  const std::vector<EventExpr> global_event;

  EXPECT_FALSE(SubstituteGlobalClockLeadingEvent(sensitivity, global_event));
  ASSERT_EQ(sensitivity.size(), 1u);
  EXPECT_EQ(sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(sensitivity[0].signal, nullptr);
  EXPECT_TRUE(IsGlobalClockLeadingEvent(sensitivity));
}

// §16.5.2: the gate of a gated clocking event `@($global_clock iff en)` belongs
// to the assertion and not to the $global_clock reference it was written
// beside, so it is carried onto the substituted event. This fails on an
// implementation that overwrites the whole sensitivity with the global clocking
// event, which drops `iff en` and evaluates the assertion on every global clock
// tick rather than on the ticks the gate admits.
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

// §16.5.2: a global clocking declaration written `@(posedge gclk iff ready)`
// carries its own gate, and the substituted event is that declaration's event,
// gate included. This fails on an implementation that clears iff_condition
// while copying, or that writes the assertion's absent gate over it, either of
// which would clock the assertion on ticks the global clocking declaration
// itself excludes.
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
