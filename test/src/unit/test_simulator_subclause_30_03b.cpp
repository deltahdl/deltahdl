// What a run installs for the specify block of §30.3, read back off the
// SimContext the run used.
//
// This is the one question the other clause-30 simulator tests do not ask.
// Each of those declares its own manager and feeds it -- `SpecifyManager mgr;`
// followed by `RegisterPathDelays(mod, f, mgr, ...)` from
// lib/cpp/test_fixtures/fixture_specify_manager.h is the shape
// test_simulator_subclause_30_07_01.cpp uses -- so each proves that
// SpecifyManager does the right thing once something hands it a design's
// declarations, and none proves that anything hands them over. Issue #3265 is
// exactly that gap: a specify block was parsed, checked, and then dropped,
// because nothing in Lowerer::Lower built a manager or registered anything
// into one. Every case here therefore elaborates a source, lowers and runs it,
// and then reads SimContext::GetSpecifyManager rather than a manager of its
// own.
//
// test_simulator_subclause_30_03a.cpp holds the other half of §30.3: a specify
// block leaves the behaviour declared around it alone.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. Each module path carries a delay no other path in its module carries
// (5, 7, 12, 10, 6, 4), and where a case asserts on pulse limits the limits
// differ from the delay they were derived from and from each other (12 with
// limits 2 and 9; 10 with limits 3 and 3). Nothing is asserted at zero except
// PathDelayCount for a module that declared no path, where zero is the claim.
// The paths are found by their two port names rather than by their position in
// GetPathDelays, so no assertion rests on a path's index matching a value.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// The module path in `mgr` that joins `src` to `dst`, or nullptr when the run
// registered no such path. SpecifyManager::GetPathDelay answers with a
// transition delay and HasPathDelay with a bool, and neither reaches
// reject_limit or error_limit, so a case whose subject is a pulse limit has to
// search GetPathDelays for the pair of port names its source declared.
const PathDelay* FindRegisteredPath(const SpecifyManager& mgr,
                                    std::string_view src,
                                    std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return &pd;
  }
  return nullptr;
}

// Elaborates, lowers and runs `src`, then returns the manager the run
// installed. Returns nullptr when the source did not elaborate, so a case
// asserts on the pointer before reading it.
SpecifyManager* RunAndTakeManager(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.GetSpecifyManager();
}

// §30.3: the module path a specify block declares is registered by the run
// itself. This is issue #3265's whole subject.
TEST(SpecifyManagerInstalledByRun, RunRegistersDeclaredModulePath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => y) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_TRUE(mgr->HasPathDelay("a", "y"));
  EXPECT_EQ(mgr->GetPathDelay("a", "y"), 5u);
}

// §32.9: $sdf_annotate reads timing data into the manager and has nowhere to
// put what it reads without one, so a run installs a manager whether or not any
// module declared a specify block. PathDelayCount is what says the run did not
// invent a path for a module that declared none.
TEST(SpecifyManagerInstalledByRun, RunWithoutSpecifyBlockStillInstallsManager) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd44;\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->PathDelayCount(), 0u);
}

// §30.7: with nothing else stated, both the reject limit and the error limit of
// a module path are set equal to the transition delay they belong to. A run
// that registered the path without applying that default would leave both at
// zero, which 7 distinguishes.
TEST(SpecifyManagerInstalledByRun, RegisteredPathStartsWithDefaultPulseLimits) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t;\n"
      "  specify\n"
      "    (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = FindRegisteredPath(*mgr, "a", "y");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 7u);
  EXPECT_EQ(path->reject_limit[0], 7u);
  EXPECT_EQ(path->error_limit[0], 7u);
}

// §30.7.1: a path-specific PATHPULSE$ specparam narrows the limits of the path
// it names, and leaves that path's transition delay alone. The source is the
// example printed under §30.7.1, cut down to the one path the specparam names.
// The value is written `(2, 9)` rather than the example's `2,9` because
// Syntax 30-4 parenthesizes it and Parser::ParseSpecparamInSpecify in
// src/parser/parser_specify.cpp requires the parentheses.
TEST(SpecifyManagerInstalledByRun, PathSpecificPathPulseNarrowsNamedPath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input clk, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* path = FindRegisteredPath(*mgr, "clk", "q");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 12u);
  EXPECT_EQ(path->reject_limit[0], 2u);
  EXPECT_EQ(path->error_limit[0], 9u);
}

// §30.7.1: a PATHPULSE$ specparam naming no module path applies to every module
// path defined in the module, and where both forms appear in one module the
// path-specific one takes precedence for the path it names. That precedence is
// what this case asserts. The two specparams are written in the order the
// example under §30.7.1 uses, the path-specific one first and the
// non-path-specific one last, which is the order in which a run that resolved
// each specparam as it read it would overwrite clk=>q with 3 and 3; the
// standard states no rule about that order, so what goes red here is the
// precedence rule and not an order rule. `PATHPULSE$ = (3)` states a reject
// limit alone, which §30.7.1 applies to the error limit as well, so both of
// data=>q's limits are 3 while its transition delay stays at 10.
TEST(SpecifyManagerInstalledByRun, NonPathSpecificPathPulseYieldsToNamedPath) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input clk, input data, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "    specparam PATHPULSE$ = (3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  const PathDelay* named = FindRegisteredPath(*mgr, "clk", "q");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[0], 12u);
  EXPECT_EQ(named->reject_limit[0], 2u);
  EXPECT_EQ(named->error_limit[0], 9u);
  const PathDelay* unnamed = FindRegisteredPath(*mgr, "data", "q");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->delays[0], 10u);
  EXPECT_EQ(unnamed->reject_limit[0], 3u);
  EXPECT_EQ(unnamed->error_limit[0], 3u);
}

// §30.7.4.1: a pulsestyle_ondetect declaration selects the on-detect style for
// the module path output it names, and on-event is the style with no
// declaration. The second half is what says the first read a declaration: a run
// that registered no pulsestyle at all answers on-event to both.
TEST(SpecifyManagerInstalledByRun, RunRegistersPulseStyleDeclaration) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    pulsestyle_ondetect y;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->ResolvePulseStyle("y"), PulseStyle::kOnDetect);

  SimFixture undeclared;
  SpecifyManager* default_mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n",
      undeclared);
  ASSERT_NE(default_mgr, nullptr);
  EXPECT_EQ(default_mgr->ResolvePulseStyle("y"), PulseStyle::kOnEvent);
}

// §30.7.4.2: a showcancelled declaration selects the showcancelled mode for the
// module path output it names, and noshowcancelled is the mode with no
// declaration. As above, the second half is what says the first read a
// declaration rather than the default answering by coincidence.
TEST(SpecifyManagerInstalledByRun, RunRegistersShowCancelledDeclaration) {
  SimFixture f;
  SpecifyManager* mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    showcancelled y;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->ResolveShowCancelled("y"), ShowCancelled::kShowcancelled);

  SimFixture undeclared;
  SpecifyManager* default_mgr = RunAndTakeManager(
      "module t(input a, output y);\n"
      "  specify\n"
      "    (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      undeclared);
  ASSERT_NE(default_mgr, nullptr);
  EXPECT_EQ(default_mgr->ResolveShowCancelled("y"),
            ShowCancelled::kNoshowcancelled);
}

}  // namespace
