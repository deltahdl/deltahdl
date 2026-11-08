#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

TEST(MultiplePathStatementRun, EveryDestinationTakesTheDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mypair(input a, input b, output y1, output "
                       "y2);\n"
                       "  assign y1 = a;\n"
                       "  assign y2 = b;\n"
                       "  specify\n"
                       "    (a, b *> y1, y2) = 4;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b;\n"
                       "  wire t1, t2;\n"
                       "  mypair u(.a(a), .b(b), .y1(t1), .y2(t2));\n"
                       "  always @(t1 or t2) if ($time >= 8)\n"
                       "    $display(\"t=%0t y1=%b y2=%b\", $time, t1, t2);\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    #10 a = 1;\n"
                       "    #10 b = 1;\n"
                       "    #10 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=14 y1=1 y2=0\nt=24 y1=1 y2=1\nt=34 y1=0 y2=1\n");
}

bool HasPath(const SpecifyManager& mgr, std::string_view src,
             std::string_view dst, uint64_t delay, uint64_t reject) {
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst && pd.delays[0] == delay &&
        pd.reject_limit[0] == reject) {
      return true;
    }
  }
  return false;
}

TEST(MultiplePathStatementRun, FirstTerminalsPulseLimitsReachEveryPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input a, input b, output y1, output y2);\n"
      "  specify\n"
      "    (a, b *> y1, y2) = 4;\n"
      "    specparam PATHPULSE$a$y1 = (1, 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  EXPECT_EQ(mgr->GetPathDelays().size(), 4u);
  EXPECT_TRUE(HasPath(*mgr, "a", "y1", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "b", "y1", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "a", "y2", 4, 1));
  EXPECT_TRUE(HasPath(*mgr, "b", "y2", 4, 1));
}

}  // namespace
