#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

struct ElaboratedTimingCheck {
  const TimingCheckDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
  bool has_errors = false;
};

const TimingCheckDecl* FirstTimingCheckIn(const ModuleItem* specify_block) {
  for (auto* si : specify_block->specify_items) {
    if (si->kind == SpecifyItemKind::kTimingCheck) return &si->timing_check;
  }
  return nullptr;
}

const TimingCheckDecl* FirstTimingCheckDecl(const CompilationUnit* cu) {
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      if (const TimingCheckDecl* decl = FirstTimingCheckIn(item)) return decl;
    }
  }
  return nullptr;
}

ElaboratedTimingCheck ElaborateTimingCheck(const std::string& module_body,
                                           const std::string& specify_body,
                                           SimFixture& f) {
  std::string code =
      "module t(input clk, input data, input clr,\n"
      "         output q);\n" +
      module_body + "  specify\n" + specify_body +
      "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  ElaboratedTimingCheck out;
  out.design = elab.Elaborate(cu->modules.back()->name);
  out.has_errors = f.diag.HasErrors();
  out.decl = FirstTimingCheckDecl(cu);
  return out;
}

void RegisterCheckUnderBothOptions(const std::string& module_body,
                                   const std::string& specify_body,
                                   SimFixture& f, SpecifyManager& on,
                                   SpecifyManager& off) {
  auto c = ElaborateTimingCheck(module_body, specify_body, f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  on.SetTimingCheckInvocationOptions({true, false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  off.SetTimingCheckInvocationOptions({false, false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
}

int64_t RequestedDelayFor(int64_t signed_limit) {
  return signed_limit < 0 ? -signed_limit : 0;
}

TEST(NegativeTimingCheckOptionFromSource, SetupholdNegativeLiteralHonored) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_TRUE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.signed_limit, -10);
  EXPECT_EQ(entry.signed_limit2, 20);
  EXPECT_EQ(entry.notifier, "ntf");

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 115));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingCheckOptionFromSource,
     SetupholdNegativeIgnoredWithoutOption) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({false, false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);

  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_FALSE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.limit, 0u);
  EXPECT_EQ(entry.limit2, 20u);

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingCheckOptionFromSource, NegativeSpecparamLimitGatedByOption) {
  SimFixture f;
  SpecifyManager on, off;
  RegisterCheckUnderBothOptions(
      "  reg ntf;\n",
      "    specparam tsetup = -10, thold = 20;\n"
      "    $setuphold(posedge clk, data, tsetup, thold, ntf);",
      f, on, off);

  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit, -10);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit2, 20);
  EXPECT_TRUE(on.CheckSetupholdViolation("clk", 100, "data", 115));

  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 0u);
}

TEST(NegativeTimingCheckOptionFromSource,
     NegativeConstantExpressionGatedPositiveLimitsUnaffected) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n",
      "    specparam unit = 5;\n"
      "    $setuphold(posedge clk, data, -(2 * unit), 20, ntf);",
      f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_EQ(mgr.GetTimingChecks().front().signed_limit, -10);
  EXPECT_TRUE(mgr.GetTimingChecks().front().negative_timing_check_enabled);

  SimFixture g;
  auto p = ElaborateTimingCheck(
      "  reg ntf;\n", "    $setuphold(posedge clk, data, 10, 20, ntf);", g);
  ASSERT_NE(p.decl, nullptr);
  ASSERT_NE(p.design, nullptr);
  ASSERT_FALSE(p.has_errors);
  LowerAndRun(p.design, g);

  SpecifyManager positive;
  positive.SetTimingCheckInvocationOptions({true, false});
  positive.AddTimingCheckUnderOptions(*p.decl, g.ctx, g.arena);
  EXPECT_FALSE(
      positive.GetTimingChecks().front().negative_timing_check_enabled);
}

TEST(NegativeTimingCheckOptionFromSource, DeclaredDelayedSignalsBecomeCopies) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, -4, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);
  EXPECT_EQ(c.decl->delayed_ref, "dclk");
  EXPECT_EQ(c.decl->delayed_data, "ddata");

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_TRUE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.signed_limit, -10);
  EXPECT_EQ(entry.signed_limit2, -4);
  const int64_t kRefDelay = RequestedDelayFor(entry.signed_limit);
  const int64_t kDataDelay = RequestedDelayFor(entry.signed_limit2);
  ASSERT_EQ(kRefDelay, 10);
  ASSERT_EQ(kDataDelay, 4);

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({false, false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 0u);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_FALSE(off.CheckSetupholdViolation("clk", 100, "data", 98));
  EXPECT_FALSE(off.CheckSetupholdViolation("clk", 100, "data", 105));

  auto delayed = ResolveDelayedSignalsUnderOptions(*c.decl, kRefDelay,
                                                   kDataDelay, {true, false});
  EXPECT_FALSE(delayed.are_copies_of_originals);
  EXPECT_EQ(delayed.ref_signal, "dclk");
  EXPECT_EQ(delayed.data_signal, "ddata");
  EXPECT_EQ(delayed.ref_delay, 10);
  EXPECT_EQ(delayed.data_delay, 4);

  auto copies = ResolveDelayedSignalsUnderOptions(*c.decl, kRefDelay,
                                                  kDataDelay, {false, false});
  EXPECT_TRUE(copies.are_copies_of_originals);
  EXPECT_EQ(copies.ref_signal, "clk");
  EXPECT_EQ(copies.data_signal, "data");
  EXPECT_EQ(copies.ref_delay, 0);
  EXPECT_EQ(copies.data_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource,
     PartialAndImplicitDelayedSignalsBecomeCopies) {
  SimFixture f;
  auto only_ref = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk);", f);
  ASSERT_NE(only_ref.decl, nullptr);
  ASSERT_NE(only_ref.design, nullptr);
  ASSERT_FALSE(only_ref.has_errors);
  LowerAndRun(only_ref.design, f);
  EXPECT_EQ(only_ref.decl->delayed_ref, "dclk");
  EXPECT_TRUE(only_ref.decl->delayed_data.empty());

  auto on =
      ResolveDelayedSignalsUnderOptions(*only_ref.decl, 10, 0, {true, false});
  EXPECT_EQ(on.ref_signal, "dclk");
  EXPECT_EQ(on.data_signal, "data");
  EXPECT_EQ(on.ref_delay, 10);

  auto off =
      ResolveDelayedSignalsUnderOptions(*only_ref.decl, 10, 0, {false, false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clk");
  EXPECT_EQ(off.ref_delay, 0);

  SimFixture g;
  auto implicit_only = ElaborateTimingCheck(
      "  reg ntf;\n", "    $setuphold(posedge clk, data, -10, 20, ntf);", g);
  ASSERT_NE(implicit_only.decl, nullptr);
  ASSERT_NE(implicit_only.design, nullptr);
  ASSERT_FALSE(implicit_only.has_errors);
  LowerAndRun(implicit_only.design, g);
  ASSERT_TRUE(implicit_only.decl->delayed_ref.empty());
  ASSERT_TRUE(implicit_only.decl->delayed_data.empty());
  auto implicit_off = ResolveDelayedSignalsUnderOptions(*implicit_only.decl, 10,
                                                        0, {false, false});
  EXPECT_TRUE(implicit_off.are_copies_of_originals);
  EXPECT_EQ(implicit_off.ref_signal, "clk");
  EXPECT_EQ(implicit_off.data_signal, "data");
  EXPECT_EQ(implicit_off.ref_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource, AllChecksOffSuppressesAndCollapses) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, true});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(mgr.GetTimingChecks().front().negative_timing_check_enabled);

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 115));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));

  auto delayed =
      ResolveDelayedSignalsUnderOptions(*c.decl, 10, 20, {true, true});
  EXPECT_TRUE(delayed.are_copies_of_originals);
  EXPECT_EQ(delayed.ref_signal, "clk");
  EXPECT_EQ(delayed.data_signal, "data");
  EXPECT_EQ(delayed.ref_delay, 0);
  EXPECT_EQ(delayed.data_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource, RecremFollowsTheSameOptionBehavior) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclr, dclk;\n",
      "    $recrem(posedge clr, posedge clk, -5, 10, ntf, , , dclr, dclk);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);
  EXPECT_EQ(c.decl->delayed_ref, "dclr");
  EXPECT_EQ(c.decl->delayed_data, "dclk");

  SpecifyManager on;
  on.SetTimingCheckInvocationOptions({true, false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_TRUE(on.CheckRecremViolation("clr", 100, "clk", 92));
  EXPECT_FALSE(on.CheckRecremViolation("clr", 100, "clk", 97));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({false, false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 92));
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 97));

  SpecifyManager all_off;
  all_off.SetTimingCheckInvocationOptions({true, true});
  all_off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(all_off.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_FALSE(all_off.CheckRecremViolation("clr", 100, "clk", 95));
}

TEST(NegativeTimingCheckOptionFromSource, RecremDelayedSignalsUnderEachOption) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclr, dclk;\n",
      "    $recrem(posedge clr, posedge clk, -5, 10, ntf, , , dclr, dclk);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  auto on = ResolveDelayedSignalsUnderOptions(*c.decl, 5, 3, {true, false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.ref_signal, "dclr");
  EXPECT_EQ(on.data_signal, "dclk");
  EXPECT_EQ(on.ref_delay, 5);
  EXPECT_EQ(on.data_delay, 3);

  auto off = ResolveDelayedSignalsUnderOptions(*c.decl, 5, 3, {false, false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clr");
  EXPECT_EQ(off.data_signal, "clk");
  EXPECT_EQ(off.ref_delay, 0);

  auto all_off = ResolveDelayedSignalsUnderOptions(*c.decl, 5, 3, {true, true});
  EXPECT_TRUE(all_off.are_copies_of_originals);
  EXPECT_EQ(all_off.ref_signal, "clr");
  EXPECT_EQ(all_off.data_signal, "clk");
  EXPECT_EQ(all_off.ref_delay, 0);
  EXPECT_EQ(all_off.data_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource, NegativeHoldOnlyGatedByOption) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, 10, -4, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager on;
  on.SetTimingCheckInvocationOptions({true, false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  const auto& entry = on.GetTimingChecks().front();
  EXPECT_TRUE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.signed_limit, 10);
  EXPECT_EQ(entry.signed_limit2, -4);
  EXPECT_TRUE(on.CheckSetupholdViolation("clk", 100, "data", 93));
  EXPECT_FALSE(on.CheckSetupholdViolation("clk", 100, "data", 98));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({false, false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 10u);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_TRUE(off.CheckSetupholdViolation("clk", 100, "data", 98));

  auto copies =
      ResolveDelayedSignalsUnderOptions(*c.decl, 0, 4, {false, false});
  EXPECT_TRUE(copies.are_copies_of_originals);
  EXPECT_EQ(copies.ref_signal, "clk");
  EXPECT_EQ(copies.data_signal, "data");
  EXPECT_EQ(copies.data_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource, NegativeMinTypMaxLimitGatedByOption) {
  SimFixture f;
  SpecifyManager on, off;
  RegisterCheckUnderBothOptions(
      "  reg ntf;\n",
      "    specparam lo = -12, mid = -10, hi = -8;\n"
      "    $setuphold(posedge clk, data, (lo:mid:hi), 20, ntf);",
      f, on, off);

  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit, -10);
  EXPECT_TRUE(on.CheckSetupholdViolation("clk", 100, "data", 115));
  EXPECT_FALSE(on.CheckSetupholdViolation("clk", 100, "data", 105));

  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 0u);
  EXPECT_TRUE(off.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingCheckOptionFromSource, BitSelectDelayedSignalsCollapse) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg [1:0] dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk[0], ddata[1]);",
      f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);
  EXPECT_EQ(c.decl->delayed_ref, "dclk");
  EXPECT_NE(c.decl->delayed_ref_expr, nullptr);
  EXPECT_EQ(c.decl->delayed_data, "ddata");
  EXPECT_NE(c.decl->delayed_data_expr, nullptr);

  auto on = ResolveDelayedSignalsUnderOptions(*c.decl, 10, 0, {true, false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.ref_signal, "dclk");
  EXPECT_EQ(on.ref_delay, 10);

  auto off = ResolveDelayedSignalsUnderOptions(*c.decl, 10, 0, {false, false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clk");
  EXPECT_EQ(off.data_signal, "data");
  EXPECT_EQ(off.ref_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource,
     DroppingTheOptionRegatesRegisteredCheck) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  ASSERT_TRUE(mgr.GetTimingChecks().front().negative_timing_check_enabled);
  ASSERT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 115));
  ASSERT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));

  mgr.SetTimingCheckInvocationOptions({false, false});
  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_FALSE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.limit, 0u);
  EXPECT_EQ(entry.limit2, 20u);
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingCheckOptionFromSource, DelayedDataOnlyDeclaredCollapses) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg ddata;\n",
      "    $setuphold(posedge clk, data, -10, 20, ntf, , , , ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);
  ASSERT_TRUE(c.decl->delayed_ref.empty());
  ASSERT_EQ(c.decl->delayed_data, "ddata");

  auto on = ResolveDelayedSignalsUnderOptions(*c.decl, 10, 0, {true, false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.data_signal, "ddata");
  EXPECT_EQ(on.ref_signal, "clk");
  EXPECT_EQ(on.ref_delay, 10);

  auto off = ResolveDelayedSignalsUnderOptions(*c.decl, 10, 0, {false, false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clk");
  EXPECT_EQ(off.data_signal, "data");
  EXPECT_EQ(off.ref_delay, 0);
}

TEST(NegativeTimingCheckOptionFromSource,
     RecremNegativeSecondLimitGatedByOption) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclr, dclk;\n",
      "    $recrem(posedge clr, posedge clk, 10, -5, ntf, , , dclr, dclk);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager on;
  on.SetTimingCheckInvocationOptions({true, false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit2, -5);
  EXPECT_TRUE(on.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_FALSE(on.CheckRecremViolation("clr", 100, "clk", 102));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({false, false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 102));
}

TEST(NegativeTimingCheckOptionFromSource, NonSpecparamNegativeLimitIsRejected) {
  SimFixture f;
  auto from_parameter = ElaborateTimingCheck(
      "  parameter integer PSETUP = -10;\n  reg ntf;\n",
      "    $setuphold(posedge clk, data, PSETUP, 20, ntf);", f);
  ASSERT_NE(from_parameter.decl, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "timing check limit operand",
                            6, "31.2"));

  SimFixture g;
  auto from_localparam = ElaborateTimingCheck(
      "  localparam integer LSETUP = -10;\n  reg ntf;\n",
      "    $setuphold(posedge clk, data, LSETUP, 20, ntf);", g);
  ASSERT_NE(from_localparam.decl, nullptr);
  EXPECT_TRUE(ReportedError(g.diag.Diagnostics(), "timing check limit operand",
                            6, "31.2"));

  SimFixture h;
  auto from_specparam = ElaborateTimingCheck(
      "  reg ntf;\n",
      "    specparam ssetup = -10;\n"
      "    $setuphold(posedge clk, data, ssetup, 20, ntf);",
      h);
  ASSERT_NE(from_specparam.decl, nullptr);
  ASSERT_FALSE(from_specparam.has_errors);
  LowerAndRun(from_specparam.design, h);

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({true, false});
  mgr.AddTimingCheckUnderOptions(*from_specparam.decl, h.ctx, h.arena);
  EXPECT_TRUE(mgr.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(mgr.GetTimingChecks().front().signed_limit, -10);
}

TEST(NegativeTimingCheckOptionFromSource, AllChecksOffSuppressesPositiveCheck) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n", "    $setuphold(posedge clk, data, 10, 20, ntf);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager checking;
  checking.SetTimingCheckInvocationOptions({false, false});
  checking.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(checking.CheckSetupholdViolation("clk", 100, "data", 95));
  EXPECT_TRUE(checking.CheckSetupholdViolation("clk", 100, "data", 105));

  SpecifyManager all_off;
  all_off.SetTimingCheckInvocationOptions({false, true});
  all_off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(all_off.CheckSetupholdViolation("clk", 100, "data", 95));
  EXPECT_FALSE(all_off.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(DelayedSignalCopies, UndeclaredDelayedSignalsCopyTheirOriginals) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top(\n"
                 "    output reg clk = 0,\n"
                 "    output reg d = 0);\n"
                 "  reg n = 0; integer t = 0;\n"
                 "  specify\n"
                 "    $setuphold(posedge clk, d, 5, 5, n, , , dclk, dd);\n"
                 "  endspecify\n"
                 "  always @(posedge dclk) t = $time;\n"
                 "  initial begin\n"
                 "    #10 d = 1;\n"
                 "    #10 clk = 1;\n"
                 "    #1 $display(\"%0d %0d\", t, dd);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "20 1\n");
}

TEST(DelayedSignalCopies, VectorAndDeclaredDelayedSignalsCopyWhole) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top(\n"
                 "    output reg clk = 0,\n"
                 "    output reg [3:0] d = 0);\n"
                 "  reg n = 0; wire dclk;\n"
                 "  specify\n"
                 "    $setuphold(posedge clk, d, 5, 5, n, , , dclk, dd);\n"
                 "  endspecify\n"
                 "  initial begin\n"
                 "    #10 d = 4'b1010; clk = 1;\n"
                 "    #1 $display(\"%b %b\", dd, dclk);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1010 1\n");
}

TEST(DelayedSignalCopies, DelayedSignalNamedByOneOfTwoChecksIsShared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg CLK = 0,\n"
                       "    output reg DATA1 = 0,\n"
                       "    output reg DATA2 = 0);\n"
                       "  specify\n"
                       "    $setuphold(posedge CLK, DATA1, 10, 20,,,, "
                       "del_CLK, del_DATA1);\n"
                       "    $setuphold(posedge CLK, DATA2, 15, 18);\n"
                       "  endspecify\n"
                       "  initial begin\n"
                       "    #50 DATA1 = 1; #50 CLK = 1;\n"
                       "    #1 $display(\"%b %b\", del_CLK, del_DATA1);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

}  // namespace
