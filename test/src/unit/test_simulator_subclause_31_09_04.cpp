#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// --- Driven from real source syntax --------------------------------------
// Every option behavior below is observed on checks built from genuine
// $setuphold (§31.3.3) and $recrem (§31.3.6) declarations: the negative limits,
// the notifier, and the optional delayed reference/data signal arguments all
// come from parsed source, and the design is elaborated and lowered first so
// that a limit written as a specparam resolves at evaluation time. The
// invocation options are the only input that does not come from source, since
// they are selected outside the design.

struct ElaboratedTimingCheck {
  const TimingCheckDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
  bool has_errors = false;
};

// The first timing check the given specify block declares, or nullptr when it
// declares none: a specify block may hold path declarations and nothing else.
const TimingCheckDecl* FirstTimingCheckIn(const ModuleItem* specify_block) {
  for (auto* si : specify_block->specify_items) {
    if (si->kind == SpecifyItemKind::kTimingCheck) return &si->timing_check;
  }
  return nullptr;
}

// The first timing check declared by any specify block anywhere in `cu`, or
// nullptr when no specify block in it declares one.
const TimingCheckDecl* FirstTimingCheckDecl(const CompilationUnit* cu) {
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      if (const TimingCheckDecl* decl = FirstTimingCheckIn(item)) return decl;
    }
  }
  return nullptr;
}

// Parses AND elaborates a module carrying the given specify body, returning its
// first timing check declaration together with the design.
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

// Registers the one timing check `module_body` / `specify_body` declares on
// two managers: `on` has the negative timing check option in force and `off`
// does not, so the same declaration is read under both settings.
//
// The design is elaborated and lowered before either registration, so a limit
// written as a specparam has resolved by the time the check is built.
void RegisterCheckUnderBothOptions(const std::string& module_body,
                                   const std::string& specify_body,
                                   SimFixture& f, SpecifyManager& on,
                                   SpecifyManager& off) {
  auto c = ElaborateTimingCheck(module_body, specify_body, f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  on.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  off.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
}

// The internal delay a check requests for a delayed copy: a negative limit is
// what has to be compensated, so its magnitude is the requested delay. Only
// whether that delay survives the invocation options is §31.9.4's concern.
int64_t RequestedDelayFor(int64_t signed_limit) {
  return signed_limit < 0 ? -signed_limit : 0;
}

// §31.9.4 C1 (accepting path): a $setuphold whose setup limit is a negative
// literal gets negative-value handling once the enabling option is selected, so
// the shifted violation window of §31.9.1 is what decides violations: a data
// transition inside (ref+10, ref+20) violates, one before the window does not.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
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

// §31.9.4 C1 (rejecting path): the same source run without the enabling option.
// The negative setup value is not handled, so the check keeps the ordinary
// two-sided behavior with that limit taken as zero -- a data transition at
// ref+5, which the negative window would have let pass, now violates, and the
// negative-window verdict at ref+15 is no longer what reports it.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);

  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_FALSE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.limit, 0u);    // negative setup not honored
  EXPECT_EQ(entry.limit2, 20u);  // positive hold unaffected

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9.4 C1: the negative limit need not be a literal. Here both limits are
// specparams -- the constant form a timing check limit admits -- resolved
// through elaboration and lowering, and the option still decides whether the
// resulting negative value is handled.
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

// §31.9.4 C1: a constant expression that evaluates negative is gated the same
// way, and a check whose limits are both positive is never turned into a
// negative-value check by the option being on.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
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
  positive.SetTimingCheckInvocationOptions(
      {/*negative=*/true, /*all_off=*/false});
  positive.AddTimingCheckUnderOptions(*p.decl, g.ctx, g.arena);
  EXPECT_FALSE(
      positive.GetTimingChecks().front().negative_timing_check_enabled);
}

// §31.9.4 C2: a model written with explicitly declared delayed reference and
// data signals can be run without the enabling option; the delayed signals then
// are copies of the originals -- the original signals, undelayed.
TEST(NegativeTimingCheckOptionFromSource, DeclaredDelayedSignalsBecomeCopies) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclk, ddata;\n",
      "    $setuphold(posedge clk, data, -10, -4, ntf, , , dclk, ddata);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);
  // The delayed-signal arguments really came from the source.
  EXPECT_EQ(c.decl->delayed_ref, "dclk");
  EXPECT_EQ(c.decl->delayed_data, "ddata");

  SpecifyManager mgr;
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  const auto& entry = mgr.GetTimingChecks().front();
  // §31.9.4 C1 for the both-limits-negative form: the option carries it.
  EXPECT_TRUE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.signed_limit, -10);
  EXPECT_EQ(entry.signed_limit2, -4);
  const int64_t kRefDelay = RequestedDelayFor(entry.signed_limit);
  const int64_t kDataDelay = RequestedDelayFor(entry.signed_limit2);
  ASSERT_EQ(kRefDelay, 10);
  ASSERT_EQ(kDataDelay, 4);

  // Without the option neither negative value is honored: both sides fall back
  // to the ordinary treatment with the limit taken as zero, which reports
  // nothing at all for this check.
  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 0u);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_FALSE(off.CheckSetupholdViolation("clk", 100, "data", 98));
  EXPECT_FALSE(off.CheckSetupholdViolation("clk", 100, "data", 105));

  // With the option in force the declared delayed signals carry their delays.
  auto delayed = ResolveDelayedSignalsUnderOptions(
      *c.decl, kRefDelay, kDataDelay, {/*negative=*/true, /*all_off=*/false});
  EXPECT_FALSE(delayed.are_copies_of_originals);
  EXPECT_EQ(delayed.ref_signal, "dclk");
  EXPECT_EQ(delayed.data_signal, "ddata");
  EXPECT_EQ(delayed.ref_delay, 10);
  EXPECT_EQ(delayed.data_delay, 4);

  // Run without it and they degenerate to copies of clk and data.
  auto copies = ResolveDelayedSignalsUnderOptions(
      *c.decl, kRefDelay, kDataDelay, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(copies.are_copies_of_originals);
  EXPECT_EQ(copies.ref_signal, "clk");
  EXPECT_EQ(copies.data_signal, "data");
  EXPECT_EQ(copies.ref_delay, 0);
  EXPECT_EQ(copies.data_delay, 0);
}

// §31.9.4 C2: the collapse applies just as much when only one delayed signal is
// declared, and when the check declares none at all (the implicit copies of
// §31.9.1).
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

  auto on = ResolveDelayedSignalsUnderOptions(
      *only_ref.decl, 10, 0, {/*negative=*/true, /*all_off=*/false});
  EXPECT_EQ(on.ref_signal, "dclk");
  // No declared delayed data signal: the copy is the implicit one, tracked
  // under the original data signal's name.
  EXPECT_EQ(on.data_signal, "data");
  EXPECT_EQ(on.ref_delay, 10);

  auto off = ResolveDelayedSignalsUnderOptions(
      *only_ref.decl, 10, 0, {/*negative=*/false, /*all_off=*/false});
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
  // Nothing declared and a negative value present: the copies the check would
  // otherwise make internally collapse without the option just the same.
  auto implicit_off = ResolveDelayedSignalsUnderOptions(
      *implicit_only.decl, 10, 0, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(implicit_off.are_copies_of_originals);
  EXPECT_EQ(implicit_off.ref_signal, "clk");
  EXPECT_EQ(implicit_off.data_signal, "data");
  EXPECT_EQ(implicit_off.ref_delay, 0);
}

// §31.9.4 C3: with the option that turns all timing checks off, a negative
// $setuphold built from real source reports nothing at all, and its delayed
// signals are copies of the originals even though the enabling option is on.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/true});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(mgr.GetTimingChecks().front().negative_timing_check_enabled);

  // Nothing is reported for either the shifted-window or the ordinary timing.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 115));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));

  auto delayed = ResolveDelayedSignalsUnderOptions(
      *c.decl, 10, 20, {/*negative=*/true, /*all_off=*/true});
  EXPECT_TRUE(delayed.are_copies_of_originals);
  EXPECT_EQ(delayed.ref_signal, "clk");
  EXPECT_EQ(delayed.data_signal, "data");
  EXPECT_EQ(delayed.ref_delay, 0);
  EXPECT_EQ(delayed.data_delay, 0);
}

// §31.9.4: the rules hold identically for $recrem (§31.3.6). The negative value
// here is the recovery limit, Syntax 31-8 writing $recrem's recovery limit
// first, and Table 31-6 gives the recovery limit the data_event role and the
// removal limit the reference_event role. So the removal limit of 10 bounds the
// side before the reference and the recovery limit of -5 bounds the side after
// it, and the window with the option on is (100 - 10, 100 + -5), which is
// (90, 95) and lies wholly before the reference.
//
// Without the option the negative value is not handled at all: it is clamped to
// zero, the after side bounds nothing, and the before side reports every
// transition within 10 of the reference. The option therefore narrows the
// window here rather than moving it, so a transition at 97 violates only with
// the option off, and one at 92 violates either way -- which is what says the
// window with the option on is not empty.
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
  on.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_TRUE(on.CheckRecremViolation("clr", 100, "clk", 92));
  EXPECT_FALSE(on.CheckRecremViolation("clr", 100, "clk", 97));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 92));
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 97));

  SpecifyManager all_off;
  all_off.SetTimingCheckInvocationOptions(
      {/*negative=*/true, /*all_off=*/true});
  all_off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(all_off.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_FALSE(all_off.CheckRecremViolation("clr", 100, "clk", 95));
}

// §31.9.4 C2/C3 for $recrem's delayed signals: with the enabling option in
// force they are NOT copies -- they are the declared ones, each carrying its
// delay -- while both the absent enabling option and the all-checks-off option
// collapse them to the original reference and data signals.
TEST(NegativeTimingCheckOptionFromSource, RecremDelayedSignalsUnderEachOption) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n  reg dclr, dclk;\n",
      "    $recrem(posedge clr, posedge clk, -5, 10, ntf, , , dclr, dclk);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  auto on = ResolveDelayedSignalsUnderOptions(
      *c.decl, 5, 3, {/*negative=*/true, /*all_off=*/false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.ref_signal, "dclr");
  EXPECT_EQ(on.data_signal, "dclk");
  EXPECT_EQ(on.ref_delay, 5);
  EXPECT_EQ(on.data_delay, 3);

  auto off = ResolveDelayedSignalsUnderOptions(
      *c.decl, 5, 3, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clr");
  EXPECT_EQ(off.data_signal, "clk");
  EXPECT_EQ(off.ref_delay, 0);

  auto all_off = ResolveDelayedSignalsUnderOptions(
      *c.decl, 5, 3, {/*negative=*/true, /*all_off=*/true});
  EXPECT_TRUE(all_off.are_copies_of_originals);
  EXPECT_EQ(all_off.ref_signal, "clr");
  EXPECT_EQ(all_off.data_signal, "clk");
  EXPECT_EQ(all_off.ref_delay, 0);
  EXPECT_EQ(all_off.data_delay, 0);
}

// §31.9.4 C1: the negative value may sit on the hold side alone. With the
// option on, the window sits wholly before the reference -- (ref-10, ref-4) --
// so a transition at ref-7 violates and one at ref-2 does not; without the
// option that same ref-2 transition is what the ordinary setup side reports.
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
  on.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  const auto& entry = on.GetTimingChecks().front();
  EXPECT_TRUE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.signed_limit, 10);
  EXPECT_EQ(entry.signed_limit2, -4);
  EXPECT_TRUE(on.CheckSetupholdViolation("clk", 100, "data", 93));
  EXPECT_FALSE(on.CheckSetupholdViolation("clk", 100, "data", 98));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 10u);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_TRUE(off.CheckSetupholdViolation("clk", 100, "data", 98));

  // And the delayed signals the model declared collapse to the originals.
  auto copies = ResolveDelayedSignalsUnderOptions(
      *c.decl, 0, 4, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(copies.are_copies_of_originals);
  EXPECT_EQ(copies.ref_signal, "clk");
  EXPECT_EQ(copies.data_signal, "data");
  EXPECT_EQ(copies.data_delay, 0);
}

// §31.9.4 C1: a timing check limit may be written as a min:typ:max constant, so
// the negative value reaching the gate can come from the selected member of a
// triple rather than from a plain constant.
TEST(NegativeTimingCheckOptionFromSource, NegativeMinTypMaxLimitGatedByOption) {
  SimFixture f;
  SpecifyManager on, off;
  RegisterCheckUnderBothOptions(
      "  reg ntf;\n",
      "    specparam lo = -12, mid = -10, hi = -8;\n"
      "    $setuphold(posedge clk, data, lo:mid:hi, 20, ntf);",
      f, on, off);

  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit, -10);
  EXPECT_TRUE(on.CheckSetupholdViolation("clk", 100, "data", 115));
  EXPECT_FALSE(on.CheckSetupholdViolation("clk", 100, "data", 105));

  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit, 0u);
  EXPECT_TRUE(off.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9.4 C2: a delayed signal argument may name a bit of a vector. Whatever
// form the declared delayed signal takes, running without the enabling option
// still leaves the check evaluating the original reference and data signals.
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

  auto on = ResolveDelayedSignalsUnderOptions(
      *c.decl, 10, 0, {/*negative=*/true, /*all_off=*/false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.ref_signal, "dclk");
  EXPECT_EQ(on.ref_delay, 10);

  auto off = ResolveDelayedSignalsUnderOptions(
      *c.decl, 10, 0, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clk");
  EXPECT_EQ(off.data_signal, "data");
  EXPECT_EQ(off.ref_delay, 0);
}

// §31.9.4 C1: the gate holds however a check came to carry negative values, not
// only at the moment its declaration was read. A check registered while the
// enabling option was in force loses its negative-value handling as soon as the
// options say the option is gone, and the ordinary treatment takes over.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  mgr.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  ASSERT_TRUE(mgr.GetTimingChecks().front().negative_timing_check_enabled);
  ASSERT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 115));
  ASSERT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));

  // Same check, run without the enabling option: the shifted window is gone.
  mgr.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  const auto& entry = mgr.GetTimingChecks().front();
  EXPECT_FALSE(entry.negative_timing_check_enabled);
  EXPECT_EQ(entry.limit, 0u);
  EXPECT_EQ(entry.limit2, 20u);
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9.4 C2: the remaining declared-delayed-signal form -- a delayed data
// signal with the delayed reference argument left empty. With the option in
// force the declared copy stands; without it, both sides are the originals.
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

  auto on = ResolveDelayedSignalsUnderOptions(
      *c.decl, 10, 0, {/*negative=*/true, /*all_off=*/false});
  EXPECT_FALSE(on.are_copies_of_originals);
  EXPECT_EQ(on.data_signal, "ddata");
  // No declared delayed reference: the internal copy stands in for clk.
  EXPECT_EQ(on.ref_signal, "clk");
  EXPECT_EQ(on.ref_delay, 10);

  auto off = ResolveDelayedSignalsUnderOptions(
      *c.decl, 10, 0, {/*negative=*/false, /*all_off=*/false});
  EXPECT_TRUE(off.are_copies_of_originals);
  EXPECT_EQ(off.ref_signal, "clk");
  EXPECT_EQ(off.data_signal, "data");
  EXPECT_EQ(off.ref_delay, 0);
}

// §31.9.4 C1: for $recrem the negative value may sit on the second limit, which
// Syntax 31-8 writes as the removal limit. Table 31-6 gives that limit the
// reference_event role, so it bounds the side before the reference, and the
// recovery limit of 10 bounds the side after. The window with the option on is
// (100 - -5, 100 + 10), which is (105, 110) and lies wholly after the
// reference.
//
// Without the option the negative removal value is clamped to zero, the before
// side bounds nothing, and the after side reports every transition within 10 of
// the reference. So a transition at 102 violates only with the option off, and
// one at 107 violates either way.
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
  on.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  on.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(on.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(on.GetTimingChecks().front().signed_limit2, -5);
  EXPECT_TRUE(on.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_FALSE(on.CheckRecremViolation("clr", 100, "clk", 102));

  SpecifyManager off;
  off.SetTimingCheckInvocationOptions({/*negative=*/false, /*all_off=*/false});
  off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(off.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(off.GetTimingChecks().front().limit2, 0u);
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 107));
  EXPECT_TRUE(off.CheckRecremViolation("clr", 100, "clk", 102));
}

// §31.9.4 C1, the constant forms the limit position does NOT admit: a negative
// value written as a module parameter or a localparam is rejected while the
// design is elaborated, so it never reaches the option gate at all. The same
// value written as a specparam elaborates cleanly and is gated as usual, which
// is the contrast this test pins down.
//
// The rejection enforces §31.2 -- "timing check limit values are constant
// expressions that can include specparams" -- so the report names §31.2 and
// not §31.9.4, and it stands on the $setuphold line rather than on the
// parameter declaration.
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
  mgr.SetTimingCheckInvocationOptions({/*negative=*/true, /*all_off=*/false});
  mgr.AddTimingCheckUnderOptions(*from_specparam.decl, h.ctx, h.arena);
  EXPECT_TRUE(mgr.GetTimingChecks().front().negative_timing_check_enabled);
  EXPECT_EQ(mgr.GetTimingChecks().front().signed_limit, -10);
}

// §31.9.4 C3: the option switches off ALL timing checks, not just those with
// negative values -- an ordinary all-positive $setuphold reports nothing under
// it, while the same check reports normally with the option absent.
TEST(NegativeTimingCheckOptionFromSource, AllChecksOffSuppressesPositiveCheck) {
  SimFixture f;
  auto c = ElaborateTimingCheck(
      "  reg ntf;\n", "    $setuphold(posedge clk, data, 10, 20, ntf);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_FALSE(c.has_errors);
  LowerAndRun(c.design, f);

  SpecifyManager checking;
  checking.SetTimingCheckInvocationOptions(
      {/*negative=*/false, /*all_off=*/false});
  checking.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_TRUE(checking.CheckSetupholdViolation("clk", 100, "data", 95));
  EXPECT_TRUE(checking.CheckSetupholdViolation("clk", 100, "data", 105));

  SpecifyManager all_off;
  all_off.SetTimingCheckInvocationOptions(
      {/*negative=*/false, /*all_off=*/true});
  all_off.AddTimingCheckUnderOptions(*c.decl, f.ctx, f.arena);
  EXPECT_FALSE(all_off.CheckSetupholdViolation("clk", 100, "data", 95));
  EXPECT_FALSE(all_off.CheckSetupholdViolation("clk", 100, "data", 105));
}

}  // namespace
