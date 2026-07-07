#include <sstream>

#include "fixture_simulator.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §21.2.2 (Syntax 21-2): every alternative of strobe_task_name dispatches to
// the strobed-monitoring path at the simulator stage. Driving all four names
// from one procedural block confirms each is recognised and each produces its
// own deferred line — i.e., $strobe-class calls are not coalesced the way
// $monitor is.
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

// §21.2.2 (Syntax 21-2): the four strobe_task_name alternatives are genuinely
// distinct dispatch targets, not aliases. Each carries its own default radix
// for a bare (unformatted) expression argument -- decimal for $strobe, binary
// for $strobeb, octal for $strobeo, hex for $strobeh -- exactly as the
// same-named $display family does (§21.2.1). Driving one 8-bit value through
// all four confirms each name renders the value in its own radix rather than a
// shared one.
TEST(IoStrobeSim, EachStrobeNameSelectsItsOwnDefaultRadix) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h2a;\n"  // 42 decimal / 00101010 binary / 052 octal / 2a hex
      "    $strobe(a);\n"
      "    $strobeb(a);\n"
      "    $strobeo(a);\n"
      "    $strobeh(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("42"), std::string::npos);      // $strobe  -> decimal
  EXPECT_NE(out.find("101010"), std::string::npos);  // $strobeb -> binary
  EXPECT_NE(out.find("052"), std::string::npos);     // $strobeo -> octal
  EXPECT_NE(out.find("2a"), std::string::npos);      // $strobeh -> hex
}

// §21.2.2: the strobe action is deferred to the end of the current simulation
// time, after all other events at that time have occurred. A $display in the
// same procedural block at the same time therefore reaches stdout first.
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

// §21.2.2: the strobe action fires in the postponed region of the current
// time slot. Anything sampled by a pre-postponed spy must not yet contain the
// strobe output; the run as a whole must.
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

// §21.2.2: $strobe accepts arguments using the same machinery as $display,
// including the %% escape sequence for a literal percent sign (§21.2.1).
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

// §21.2.2: the deferred action must follow every other event at the same time,
// so a non-blocking update queued earlier in the same procedural block must
// have already taken effect before the strobe samples its arguments. If the
// strobe fired before the NBA region, the printed value would be the
// pre-update 0.
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

// §21.2.2: a $strobe of a $sampled value prints the value from the preponed
// region of the current time step. Because the strobe fires in the postponed
// region of that same time step, the variable's value-as-of-this-step is the
// value that reaches the output.
TEST(IoStrobeSim, StrobeOfSampledValueUsesCurrentStep) {
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
  EXPECT_EQ(out, "34\n");
}

}  // namespace
