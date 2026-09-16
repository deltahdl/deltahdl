#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/sequence_methods.sv around one destination
// sequence: the clause's e1 on sysclk, rising at 8, 24, 40, ..., ends at
// 56, and a destination sequence on the clock its body names; the process
// counts the end points the destination reaches and keeps the time of the
// last. clk rises at 5, 15, ..., never together with sysclk.
std::string SequenceMethodSource(const std::string& destination) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic sysclk = 0;\n"
         "  logic a = 0, b = 0, c = 0;\n"
         "  logic reset = 0, inst = 0, branch_back = 0;\n"
         "  logic reset1 = 0, branch_back1 = 0;\n"
         "  int ends = 0;\n"
         "  int last_end = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1;\n"
         "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e2_with_arg(sequence subseq);\n"
         "    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 "
         "branch_back;\n"
         "  endsequence\n"
         "  sequence dest;\n" +
         destination +
         "  endsequence\n"
         "  initial forever begin\n"
         "    wait (dest.triggered);\n"
         "    ends++;\n"
         "    last_end = $time;\n"
         "    #1;\n"
         "  end\n"
         "  initial begin\n"
         "    #10 a = 1;\n"
         "    #10 reset = 1;\n"
         "    #10 reset = 0; b = 1;\n"
         "    #5 inst = 1;\n"
         "    #10 inst = 0;\n"
         "    #5 b = 0; c = 1; reset1 = 1;\n"
         "    #10 reset1 = 0;\n"
         "    #5 c = 0; branch_back = 1;\n"
         "    #5 branch_back1 = 1;\n"
         "    #5 branch_back = 0;\n"
         "    #5 branch_back1 = 0;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// The end points the destination sequence reached, and the time of the
// last.
struct EndPoints {
  uint64_t ends;
  uint64_t last_end;
};

EndPoints EndPointsOf(const std::string& destination) {
  SimFixture f;
  auto* ends = RunAndFindVar(SequenceMethodSource(destination), f, "ends");
  if (ends == nullptr) return {~0ull, ~0ull};
  Variable* last_end = f.ctx.FindVariable("last_end");
  return {ends->value.ToUint64(), last_end->value.ToUint64()};
}

// §16.13.6: triggered on a named sequence is true at the time step its end
// point is reached, 56 for e1, so the clause's e2, on e1's clock, reads it
// there and ends at branch_back, 72.
TEST(SequenceMethods, TriggeredOnANamedSequenceReadsItsEndPoint) {
  EndPoints e2 = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 "
      "branch_back;\n");
  EXPECT_EQ(e2.ends, 1u);
  EXPECT_EQ(e2.last_end, 72u);
}

// §16.13.6: matched on a named sequence stores its end point until the
// first tick of the reading clock after it, 65 on clk for e1's 56, so the
// clause's e3 reads it there and ends at branch_back1, 75.
TEST(SequenceMethods, MatchedOnANamedSequenceStoresItsEndPointForAnotherClock) {
  EndPoints e3 = EndPointsOf(
      "    @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;\n");
  EXPECT_EQ(e3.ends, 1u);
  EXPECT_EQ(e3.last_end, 75u);
}

// §16.13.6: triggered on a formal of type sequence reads the end point of
// the actual, e1's body passed to e2_with_arg, so the clause's e4 ends
// where e2 does, 72.
TEST(SequenceMethods, TriggeredOnASequenceFormalReadsTheActualsEndPoint) {
  EndPoints e4 =
      EndPointsOf("    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 1u);
  EXPECT_EQ(e4.last_end, 72u);
}

// §16.13.6: the formal's triggered is the actual's end point and not the
// instance's own progress: an actual that never ends, $rose(reset1) at 56
// followed by b at 72 where b is low, leaves it false and the instance
// never ends.
TEST(SequenceMethods, AnActualThatNeverMatchesLeavesTheFormalsTriggeredFalse) {
  EndPoints e4 = EndPointsOf(
      "    e2_with_arg(@(posedge sysclk) $rose(reset1) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 0u);
}

}  // namespace
