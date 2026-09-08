#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArraySimulation, DynamicElementCreation) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, MultipleElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArraySimulation, OverwriteElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 100;\n"
      "    aa[7] = 200;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArraySimulation, NoStorageAllocatedUntilUsed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial result = aa.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArraySimulation, RefArgAllocatesNonexistentEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic inc_ref(ref int x);\n"
      "    x = x + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    inc_ref(aa[5]);\n"
      "    result = aa.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// §7.8 — the element data type may be any type allowed for a fixed-size array,
// not only a plain int. Drive a packed-vector element type end-to-end and read
// the stored value back to confirm the declared element type governs storage.
TEST(AssocArraySimulation, VectorElementStoredAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 8'hAB;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

// §7.8 — copying a whole associative array is one of the two exceptions to the
// "select an element first" rule. This drives the copy end-to-end (real
// declaration + whole-array assignment syntax) and confirms the destination
// receives the source's entries, not just that the copy elaborates.
TEST(AssocArraySimulation, WholeArrayCopyDuplicatesEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 77;\n"
      "    bb = aa;\n"
      "    result = bb[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// §9.4.2 has a non-edge implicit event "detected on any change in the value of
// the expression" and names an aggregate element as a lawful operand of one:
// "Object (class instance) members or aggregate elements can be any type as
// long as the result of the expression is a singular value". The clause puts
// the duty on the writer -- "Changing the value of object data members,
// aggregate elements ... shall cause the event expression to be reevaluated" --
// and an associative array's entries live outside the variable an @(aa[3]) arms
// its watcher on, so the write has to announce the change itself.
TEST(AssocArraySimulation, AssocElementWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 1u);
}

// The same event on the other writer: `aa[3][3:0]` is §7.8.7's write to bits of
// an element, which goes through TryWriteAssocElementBits rather than the
// whole-element store, so a notification placed on one does not reach the
// other. Two changes after the control armed, so the count discriminates
// between a fix that reached both writers and one that reached only the first.
TEST(AssocArraySimulation,
     AssocElementBitSelectWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 aa[3][3:0] = 4'hA;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 2u);
}

// The other awaiter route onto the same notification: an inferred sensitivity
// list reduces a select read to its base name, so the always_comb arms an
// AnyChangeAwaiter on `aa` and resumes on the notification alone -- the
// comparison that awaiter makes is skipped for a name FindAssocArray answers,
// the array's own variable holding no element value to compare.
TEST(AssocArraySimulation, AssocElementWriteWakesAnAlwaysCombThatReadsIt) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  logic [7:0] b;\n"
      "  always_comb b = aa[3];\n"
      "  initial begin\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 0xF0u);
}

}  // namespace
