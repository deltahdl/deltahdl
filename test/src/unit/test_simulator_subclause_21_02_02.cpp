#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {
TEST(IoStrobeSim, AllStrobeTaskNamesDispatchToStrobeMachinery) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h2a;\n"
      "    $strobe(\"a=%h\", a);\n"
      "    $strobeb(\"a=%h\", a);\n"
      "    $strobeo(\"a=%h\", a);\n"
      "    $strobeh(\"a=%h\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=2a\na=2a\na=2a\na=2a\n");
}

TEST(IoStrobeSim, EachStrobeNameSelectsItsOwnDefaultRadix) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h2a;\n"
      "    $strobe(a);\n"
      "    $strobeb(a);\n"
      "    $strobeo(a);\n"
      "    $strobeh(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("42"), std::string::npos);
  EXPECT_NE(out.find("101010"), std::string::npos);
  EXPECT_NE(out.find("052"), std::string::npos);
  EXPECT_NE(out.find("2a"), std::string::npos);
}

TEST(IoStrobeSim, StrobeDeferredAfterSameTimeDisplay) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $display(\"first\");\n"
      "    $strobe(\"second\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "first\nsecond\n");
}

TEST(IoStrobeSim, StrobeFiresInPostponedRegion) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());

  SimFixture f;
  std::string snapshot_pre_postponed;
  auto* spy = f.scheduler.GetEventPool().Acquire();
  spy->callback = [&]() { snapshot_pre_postponed = captured.str(); };
  f.scheduler.ScheduleEvent({0}, Region::kPrePostponed, spy);

  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $strobe(\"STROBE_MARK\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  std::cout.rdbuf(old_buf);

  EXPECT_EQ(snapshot_pre_postponed.find("STROBE_MARK"), std::string::npos);
  EXPECT_NE(captured.str().find("STROBE_MARK"), std::string::npos);
}

TEST(IoStrobeSim, StrobeAppliesDisplayStyleFormatEscape) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $strobe(\"a=%h%%\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=5%\n");
}

TEST(IoStrobeSim, StrobeObservesNonBlockingUpdate) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] y;\n"
      "  initial begin\n"
      "    y = 0;\n"
      "    y <= 8'h2a;\n"
      "    $strobe(\"y=%h\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=2a\n");
}

TEST(IoStrobeSim, StrobeOfSampledValueUsesThePreponedValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h11;\n"
      "    #10 x = 8'h22;\n"
      "    $strobe(\"%0d\", $sampled(x));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "17\n");
}

TEST(IoStrobeSim, StrobeInAClassMethodReadsTheMethodsObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class W;\n"
      "    int v = 1;\n"
      "    task run;\n"
      "      $strobe(\"bare %0d this %0d\", v, this.v);\n"
      "      v = 4;\n"
      "    endtask\n"
      "  endclass\n"
      "  W w = new;\n"
      "  initial w.run();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "bare 4 this 4\n");
}

TEST(IoStrobeSim, StrobeInAResumedClassTaskReadsTheMethodsObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  event ev;\n"
      "  class W;\n"
      "    int v = 1;\n"
      "    task run;\n"
      "      $display(\"before %0d at %0t\", v, $time);\n"
      "      #3 v = 2;\n"
      "      $display(\"after %0d at %0t\", v, $time);\n"
      "      @ev;\n"
      "      v = 3;\n"
      "      $display(\"woke %0d at %0t\", v, $time);\n"
      "      $strobe(\"strobe %0d at %0t\", v, $time);\n"
      "      v = 4;\n"
      "    endtask\n"
      "  endclass\n"
      "  W w = new;\n"
      "  initial w.run();\n"
      "  initial #5 -> ev;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "before 1 at 0\nafter 2 at 3\nwoke 3 at 5\nstrobe 4 at 5\n");
}

TEST(IoStrobeSim, StrobeReadsTheScopeOfItsCall) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub;\n"
      "  int x = 3;\n"
      "  task automatic tk;\n"
      "    int l = 9;\n"
      "    $strobe(\"%m %0d %0d\", x, l);\n"
      "  endtask\n"
      "  initial begin : blk\n"
      "    $strobe(\"%m\");\n"
      "    tk();\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    initial $strobe(\"%m\");\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t.u.blk\nt.u.blk.tk 3 9\nt.u.g[0]\nt.u.g[1]\n");
}

}  // namespace
