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

// §16.9.3 makes $sampled "the sampled value of its argument (see 16.5.1)", and
// §16.5.1 makes that the value in the Preponed region of the time slot -- what
// the slot began with, before anything in it wrote. The write to 8'h22 and the
// strobe stand in the same slot at time 10, so what the strobe prints is the
// 8'h11 the slot began with, whichever region the strobe itself fires in.
//
// This case asserted 34 -- the live value -- and so pinned $sampled as an
// identity on its argument. That is what it was: the function evaluated its
// argument and returned it.
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

// §21.2.2 (printed page 664) with §8.6 and §8.11: a $strobe inside a class
// method displays its arguments at the end of the step as the method sees
// them -- the object's property named bare and as this.v -- after the method
// has returned and after the write that follows the call. Each read 0: the
// deferred text was produced with no object in scope.
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

// §21.2.2 with §13.3: the same after the method has suspended on a delay and
// an event wait, the object being the one the resumed method runs on.
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

// §21.2.2 with §21.2.1.5 and §13.3.2: the deferred text reads the scope the
// call was made in -- %m names the named block, the task inside it, and each
// generate block instance, and an automatic task's local keeps the value it
// held. %m named the last process to have run, t.u.g[1], for every line, and
// the local read 0.
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
