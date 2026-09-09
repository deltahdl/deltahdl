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

// §7.8's declaration is a declaration wherever it is written, and §6.21 puts a
// variable declared inside a subroutine among the ones a subroutine declares.
// SimContext::CreateAssocArray was reached from the lowering of a module's own
// variables and from an associative-array formal argument and from nowhere
// else, so an array declared among a subroutine's statements existed for no
// name: every index write stored nothing and every read answered the element
// type's default, with nothing reported (#3614).

// §7.8: "allocate storage for elements only when they are used". The write is
// what uses the element, and the read is what says the storage it allocated is
// the storage the key reaches.
TEST(AssocArraySimulation, ADeclarationInsideAFunctionBuildsTheArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keep();\n"
      "    int aa [int];\n"
      "    aa[7] = 42;\n"
      "    return aa[7];\n"
      "  endfunction\n"
      "  initial result = keep();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8.6's copy of a whole associative array between two of them declared the
// same way, which is the form #3496 could not write while this was open:
// TryAssocCopyAssign asks SimContext::FindAssocArray for both names and
// declined for both.
TEST(AssocArraySimulation, ACopyBetweenTwoDeclaredInsideAFunction) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int copy();\n"
      "    int src [int];\n"
      "    int dst [int];\n"
      "    src[7] = 42;\n"
      "    dst = src;\n"
      "    return dst[7];\n"
      "  endfunction\n"
      "  initial result = copy();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8's index type decides which values are one element, so a `string` index
// is a different map from an integral one and the array a subroutine declares
// is keyed by the type its dimension names.
TEST(AssocArraySimulation, AStringKeyedArrayInsideAFunctionKeysByTheString) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keyed();\n"
      "    int aa [string];\n"
      "    aa[\"seven\"] = 42;\n"
      "    return aa[\"seven\"];\n"
      "  endfunction\n"
      "  initial result = keyed();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// The same declaration among a module's items, which is the path
// Lowerer::LowerVar serves. Without it a fix that moved the creation rather
// than adding one would pass the three above and take this away.
TEST(AssocArraySimulation, TheSameDeclarationAmongAModulesItemsStillBuildsOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 42;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
