#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

PathDelay MakePathWithDelays(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(ApplyPulseControlOverride, PreservesPropagationDelays) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 10u);
}

// --- §30.7.1 resolution from real source. The PATHPULSE$ specparam rules --
// reject-only mirrors to the error limit, a non-path-specific specparam reaches
// every path, and a path-specific specparam takes precedence -- depend on how
// the specparams and module paths are written, so they are exercised on a
// SpecifyManager built from actual parsed/elaborated source rather than a hand
// assembled state.

// Parses + elaborates a module (fixed ports clk/data/pre/q), then seeds a
// SpecifyManager: one default-limit PathDelay per module path declaration
// (§30.4.2/§30.5.1), and every PATHPULSE$ specparam evaluated and applied
// through the production resolver (§30.7.1).
void BuildResolvedSpecify(const std::string& specify_body, SimFixture& f,
                          SpecifyManager& mgr,
                          const std::string& module_items = "") {
  std::string code = "module t(input clk, input data, input pre, output q);\n" +
                     module_items + "  specify\n" + specify_body +
                     "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  LowerAndRun(design, f);

  for (auto* item : cu->modules.back()->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) {
        PathDelay pd = BuildPathDelayFromDecl(si->path, f.ctx, f.arena);
        InitDefaultPulseLimits(pd);  // §30.7 default: limits equal the delay
        mgr.AddPathDelay(pd);
      }
    }
  }
  RegisterPathPulseSpecparams(*cu->modules.back(), f, mgr);
}

const PathDelay* FindPath(const SpecifyManager& mgr, std::string_view src,
                          std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return &pd;
  }
  return nullptr;
}

// §30.7.1: a lone reject limit applies to both the reject and error limit. The
// specparam is written with a single value, so has_error is false and the
// resolver mirrors the reject limit onto the error limit across every slot.
TEST(PulseControlResolution, RejectOnlyMirrorsErrorFromSource) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (4);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(p->reject_limit[i], 4u);
    EXPECT_EQ(p->error_limit[i], 4u);
  }
}

// §30.7.1: when no module path is specified, the limits apply to every module
// path in the module. Both declared paths receive the module-wide limits.
TEST(PulseControlResolution, NonPathSpecificAppliesToEveryPath) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$ = (3, 7);",
      f, mgr);
  const PathDelay* a = FindPath(mgr, "clk", "q");
  const PathDelay* b = FindPath(mgr, "data", "q");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(a->reject_limit[i], 3u);
    EXPECT_EQ(a->error_limit[i], 7u);
    EXPECT_EQ(b->reject_limit[i], 3u);
    EXPECT_EQ(b->error_limit[i], 7u);
  }
}

// §30.7.1: a path-specific PATHPULSE$ takes precedence over a non-path-specific
// one for the path it names, regardless of declaration order. The module-wide
// specparam is written LAST here, yet clk=>q still keeps its path-specific
// limits while the unnamed data=>q path falls back to the module-wide value.
TEST(PulseControlResolution, PathSpecificWinsRegardlessOfOrder) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "    specparam PATHPULSE$ = (3);",
      f, mgr);
  const PathDelay* named = FindPath(mgr, "clk", "q");
  const PathDelay* other = FindPath(mgr, "data", "q");
  ASSERT_NE(named, nullptr);
  ASSERT_NE(other, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(named->reject_limit[i], 2u);
    EXPECT_EQ(named->error_limit[i], 9u);
    EXPECT_EQ(other->reject_limit[i], 3u);  // module-wide reject-only mirror
    EXPECT_EQ(other->error_limit[i], 3u);
  }
}

// Input form: a limit_value is a constant_mintypmax_expression, so it may be a
// specparam constant (11.2.1) rather than a literal. The resolved limit equals
// the specparam's value.
TEST(PulseControlResolution, LimitValueFromSpecparamConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    specparam lim = 5;\n"
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (lim);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 5u);
  EXPECT_EQ(p->error_limit[0], 5u);
}

// §30.7.1, multiple-path declaration: a PATHPULSE$ is recognized only for the
// first path input/output terminal, and one that names a non-first terminal is
// ignored. Driven from a real `*>` multiple-path declaration (clk, pre *> q):
// the specparam naming the first input terminal (clk) sets the limits, while
// the one naming the non-first input terminal (pre) leaves them unchanged.
TEST(PulseControlResolution, MultiPathFirstTerminalAppliesNonFirstIgnored) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk, pre *> q) = 4;\n"
      "    specparam PATHPULSE$clk$q = (1, 2);\n"
      "    specparam PATHPULSE$pre$q = (9);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  // First-terminal specparam applied; the non-first (pre) specparam was ignored
  // rather than overwriting the limits with its reject value of 9.
  EXPECT_EQ(p->reject_limit[0], 1u);
  EXPECT_EQ(p->error_limit[0], 2u);
}

// Input form: a limit_value is a constant_mintypmax_expression, so it may be a
// module parameter (11.2.1) -- a different evaluation path than a literal or a
// specparam. The resolved limit equals the parameter's value.
TEST(PulseControlResolution, LimitValueFromParameterConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (P);",
      f, mgr, "  parameter P = 6;\n");
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 6u);
  EXPECT_EQ(p->error_limit[0], 6u);
}

// Input form: a limit_value that is a localparam constant -- again a distinct
// evaluation path from a parameter or specparam. The resolved limit equals the
// localparam's value.
TEST(PulseControlResolution, LimitValueFromLocalparamConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (L);",
      f, mgr, "  localparam L = 7;\n");
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 7u);
  EXPECT_EQ(p->error_limit[0], 7u);
}

// Input form: a limit_value written as a min:typ:max triple. Under the default
// delay mode the typical member is selected and becomes the pulse limit.
TEST(PulseControlResolution, LimitValueMintypmaxSelectsTypical) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (2:5:9);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 5u);
  EXPECT_EQ(p->error_limit[0], 5u);
}

// §30.7.1: a path-specific PATHPULSE$ overrides only the path it names; a
// sibling path with no PATHPULSE$ of its own keeps its default limits (equal to
// its §30.5.1 delay) rather than inheriting the named path's limits.
TEST(PulseControlResolution, PathSpecificAffectsOnlyNamedPath) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 8;\n"
      "    specparam PATHPULSE$clk$q = (2, 5);",
      f, mgr);
  const PathDelay* named = FindPath(mgr, "clk", "q");
  const PathDelay* other = FindPath(mgr, "data", "q");
  ASSERT_NE(named, nullptr);
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(named->reject_limit[0], 2u);
  EXPECT_EQ(named->error_limit[0], 5u);
  EXPECT_EQ(other->reject_limit[0],
            8u);  // default, untouched by the clk=>q spec
  EXPECT_EQ(other->error_limit[0], 8u);
}

// §30.7.1: a path-specific PATHPULSE$ that names no existing module path
// matches nothing and is ignored -- the real path keeps its default limits
// (equal to the §30.5.1 delay) untouched.
TEST(PulseControlResolution, UnmatchedPathSpecificIsIgnored) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$data$q = (2, 4);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  // Default limits from the delay of 12 remain, unaffected by the ignored
  // data=>q specparam.
  EXPECT_EQ(p->reject_limit[0], 12u);
  EXPECT_EQ(p->error_limit[0], 12u);
}

// §30.7.1's worked example, run rather than inspected. Issue #3384 is that the
// example's own last line, `PATHPULSE$ = 3;`, was rejected, and the prose above
// the example reads the 3 back off exactly the path asserted here: "The path
// (data=>q) is not explicitly defined in any of the PATHPULSE$ declarations;
// therefore, it acquires reject and error limit of 3, as defined by the last
// PATHPULSE$ declaration." A parse test alone would pass against a parser that
// accepted the unparenthesized form and dropped the value, so this is the case
// that says the 3 arrived; both limits are asserted because §30.7.1 mirrors a
// lone reject limit onto the error limit.
//
// Nothing of the specify block is trimmed -- all three module path
// declarations and all three specparams are the example's, verbatim. What is
// added is the module header the example does not print: §30.4.1 requires a
// module path source to be a net connected to an input or inout port and a
// destination to be connected to an output or inout port, and
// CheckSpecifyPathTerminal in src/elaborator/elaborator_validate_specify.cpp
// rejects a path terminal that is a declared local signal, so clk, data, clr
// and pre are input ports and q is an output port.
//
// The example's numbers are kept as printed. 3 is the value the claim rests
// on, and it differs from every other limit and delay in the source (12, 10, 4,
// 2, 9), so a limit taken from the wrong specparam or from a path's default
// (its own delay of 10) is caught. Nothing asserts on the 0 in `(0,4)`, since a
// reject limit of 0 and an unset one read the same.
TEST(PulseControlResolution, StandardExampleUnparenthesizedLimitReachesPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input clk, input data, input clr, input pre, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    (clr, pre *> q) = 4;\n"
      "\n"
      "  specparam\n"
      "      PATHPULSE$clk$q = (2,9),\n"
      "      PATHPULSE$clr$q = (0,4),\n"
      "      PATHPULSE$ = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  SpecifyManager* installed = f.ctx.GetSpecifyManager();
  ASSERT_NE(installed, nullptr);
  const PathDelay* unnamed = FindPath(*installed, "data", "q");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->reject_limit[0], 3u);
  EXPECT_EQ(unnamed->error_limit[0], 3u);
}

}  // namespace
