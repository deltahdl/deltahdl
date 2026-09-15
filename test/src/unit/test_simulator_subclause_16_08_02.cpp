#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The source the cases share: clk rises at 5, 15, 25, ...; the stimulus is
// what `drive` writes between the ticks; and a process counts the ticks at
// which the named sequence `rule`, declared as `decls` has it, reaches its end
// point, keeping the last such time.
std::string LocalSource(const std::string& decls, const std::string& drive) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic c = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  int data = 0;\n"
         "  int data_in = 0;\n"
         "  int data_out = 0;\n"
         "  int do1 = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls + "  initial begin\n" + drive +
         "    #40 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

// §16.10 as §16.8.2 rests on it: a local variable the body declares is
// assigned by a match item where its operand holds and read by a later
// operand of the same attempt. v1 takes data's 5 at the tick at 15, and the
// sequence ends where do1 reads 5 two ticks later, not where it reads 6.
TEST(LocalVariableFormals, BodyLocalAssignedByAMatchItemIsReadLater) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##2 (do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 c = 0; data = 6; do1 = 6;\n"
                  "    #10 do1 = 5;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

// §16.8.2: a new copy of each local variable is created at the beginning of
// each attempt, so two attempts in flight hold their own: c holds at the ticks
// at 15 and 25 with data at 5 and then 6, and each attempt ends two ticks on
// where do1 reads its own capture, at 35 and at 45.
TEST(LocalVariableFormals, EachAttemptHoldsItsOwnCopy) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##2 (do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 data = 6;\n"
                  "    #10 c = 0; do1 = 5;\n"
                  "    #10 do1 = 6;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

// §16.8.2: a local variable formal argument of direction input is
// initialized from its actual at the beginning of each attempt of the
// instance, before the instance's first operand is evaluated, and keeps that
// value: sub(data) holds data's 5 from the tick at 15 through the tick at 25
// though data reads 6 there, so the sequence ends where do1 reads 5.
TEST(LocalVariableFormals, InputLocalFormalIsInitializedFromTheActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(LocalSource("  sequence sub(local input int lv);\n"
                                         "    c ##1 (do1 == lv);\n"
                                         "  endsequence\n"
                                         "  sequence rule;\n"
                                         "    @(posedge clk) sub(data);\n"
                                         "  endsequence\n",
                                         "    #10 c = 1; data = 5;\n"
                                         "    #10 c = 0; data = 6; do1 = 5;\n"
                                         "    #10 do1 = 6;\n"
                                         "    #10 do1 = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.8.2's example, its repetition left out: sub_seq2's inout lv is
// initialized from seq2's v1, incremented by data_in where !a holds, and
// assigned back to v1 when the instance matches, so seq2's last operand reads
// v1 as 8, the 5 captured from data plus the 3 of data_in, where do1 reads 8
// at the tick at 55. Assigned back nowhere, v1 would still read 5 there.
TEST(LocalVariableFormals, InoutLocalFormalIsAssignedBackAtTheMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence sub_seq2(local inout int lv);\n"
                  "    (a ##1 !a, lv += data_in) ##1 b && (data_out == lv);\n"
                  "  endsequence\n"
                  "  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##1 sub_seq2(v1) ##1 "
                  "(do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 c = 0; a = 1;\n"
                  "    #10 a = 0; data_in = 3;\n"
                  "    #10 b = 1; data_out = 8;\n"
                  "    #10 b = 0; do1 = 8;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

}  // namespace
