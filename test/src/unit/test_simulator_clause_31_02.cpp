// §31.2: Overview

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

using namespace delta;

struct SimA705Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimA705Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// All 12 kinds can be stored in SpecifyManager
TEST(SimA705, RuntimeAllTwelveKinds) {
  SpecifyManager mgr;
  TimingCheckKind kinds[] = {
      TimingCheckKind::kSetup,     TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,   TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,      TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew,  TimingCheckKind::kPeriod,
      TimingCheckKind::kWidth,     TimingCheckKind::kNochange,
  };
  for (auto kind : kinds) {
    TimingCheckEntry tc;
    tc.kind = kind;
    tc.ref_signal = "clk";
    tc.data_signal = "data";
    tc.limit = 10;
    mgr.AddTimingCheck(tc);
  }
  EXPECT_EQ(mgr.TimingCheckCount(), 12u);
  for (uint32_t i = 0; i < 12; ++i) {
    EXPECT_EQ(mgr.GetTimingChecks()[i].kind, kinds[i]);
  }
}

}  // namespace
