#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_statement_in_every_procedure.h"

using namespace delta;

namespace {

constexpr const char* kSumLoops[] = {
    "for (int i = 1; i <= 3; i++) r += i;\n",
    "begin int i; i = 0; repeat (3) begin i++; r += i; end end\n",
    "begin int i; i = 1; while (i <= 3) begin r += i; i++; end end\n",
    "begin int i; i = 1; do begin r += i; i++; end while (i <= 3); end\n",
    ("begin int i; i = 0; forever begin i++; r += i; if (i == 3) break; end "
     "end\n"),
    "begin int a [1:3]; foreach (a[i]) r += i; end\n"};

TEST(LoopStatementSim, EveryKindOfLoopRunsInEveryKindOfProcedure) {
  for (const char* loop : kSumLoops) {
    SimFixture f;
    EXPECT_EQ(RunCapture(StatementInEveryProcedure(loop), f),
              "6 6 6 6 6\nG 6\nI 6\nP 6\n")
        << loop;
    EXPECT_EQ(f.diag.WarningCount(), 0u) << loop;
  }
}

}  // namespace
