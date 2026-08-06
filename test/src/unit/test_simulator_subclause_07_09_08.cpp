// Tests for IEEE 1800-2023 clause 7.9.8 -- arguments to the associative array
// traversal methods first(), last(), next(), and prev(). The clause adds two
// rules on top of the four methods (this pass's dependencies 7.9.4-7.9.7): the
// argument must be assignment compatible with the array's index type, and when
// the argument's integral type is narrower than the index type the method
// returns -1 and truncates the assigned index to fit into the argument (keeping
// the least significant bits). Both effects depend on how the inputs are
// produced -- the argument's width comes from its declaration and the index
// width comes from the array's index-type declaration -- so every test builds
// the array and the index variable from real declaration + indexed-write source
// (dependency 7.8) and drives it through parse -> elaborate -> lower -> run,
// observing the value the method returns and the (possibly truncated) index it
// writes back through the ref argument (dependency 13.5.1). The
// assignment-compatibility half of the clause is a static rule exercised by the
// elaborator tests in this pass's canonical elaborator file.

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The clause's worked example: an int index (32 bits) with a byte argument
// (8 bits). first() finds the sole key 1000 but the argument cannot hold it, so
// the method returns -1 and truncates the returned key to the argument's width,
// keeping the least significant bits: status is -1 and ix is 1000 & 0xFF ==
// 232.
TEST(AssocTraversalArgs, FirstReturnsNegOneAndTruncatesLRMExample) {
  const char* src =
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[1000] = 7;\n"
      "    status = aa.first(ix);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);  // int holding -1
  EXPECT_EQ(RunAndGet(src, "ix"), 232u);
}

// The narrow-argument rule applies to last() as well: last() picks the largest
// key, which still cannot fit in a byte, so it returns -1 and truncates.
TEST(AssocTraversalArgs, LastReturnsNegOneAndTruncates) {
  uint64_t status = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[300] = 1;\n"
      "    aa[500] = 2;\n"
      "    status = aa.last(ix);\n"
      "  end\n"
      "endmodule\n",
      "status");
  EXPECT_EQ(status, 0xFFFFFFFFull);
  uint64_t ix = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[300] = 1;\n"
      "    aa[500] = 2;\n"
      "    status = aa.last(ix);\n"
      "  end\n"
      "endmodule\n",
      "ix");
  EXPECT_EQ(ix, 500u & 0xFFu);  // 500 & 0xFF == 244
}

// next() also obeys the rule. Seeding the byte argument with 10, the successor
// key by value is 300; it does not fit in a byte, so next() returns -1 and
// writes 300 & 0xFF == 44.
TEST(AssocTraversalArgs, NextReturnsNegOneAndTruncates) {
  const char* src =
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[10] = 1;\n"
      "    aa[300] = 2;\n"
      "    ix = 8'd10;\n"
      "    status = aa.next(ix);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);
  EXPECT_EQ(RunAndGet(src, "ix"), 300u & 0xFFu);  // 44
}

// prev() obeys the rule too, and this case isolates a key point: the -1 return
// is governed by the argument's *type* being narrower than the index type, not
// by whether the particular key value overflowed. Here prev(200) yields key 10,
// which fits in a byte, yet the method still returns -1 because a byte argument
// is narrower than the int index type.
TEST(AssocTraversalArgs, PrevReturnsNegOneEvenWhenValueFits) {
  const char* src =
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[10] = 1;\n"
      "    aa[300] = 2;\n"
      "    ix = 8'd200;\n"
      "    status = aa.prev(ix);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);
  EXPECT_EQ(RunAndGet(src, "ix"), 10u);
}

// Contrast: an argument whose type is exactly as wide as the index type is not
// narrower, so the method returns 1 (not -1) and assigns the full key.
TEST(AssocTraversalArgs, EqualWidthArgReturnsOneNoTruncation) {
  const char* src =
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[70000] = 5;\n"
      "    status = aa.first(k);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 1u);
  EXPECT_EQ(RunAndGet(src, "k"), 70000u);
}

// Contrast: an argument wider than the index type is not narrower either, so
// the method returns 1 and the full (small) key is assigned without truncation.
// Here the index type is a byte (8 bits) and the argument is an int (32 bits).
TEST(AssocTraversalArgs, WiderArgReturnsOneNoTruncation) {
  const char* src =
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  int k;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[200] = 9;\n"
      "    status = aa.first(k);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 1u);
  EXPECT_EQ(RunAndGet(src, "k"), 200u);
}

// A shortint index (16 bits) with a byte argument (8 bits): the argument type
// is narrower than the index type, so first() returns -1 and truncates the key
// to the low 8 bits. 300 & 0xFF == 44.
TEST(AssocTraversalArgs, ShortintIndexTruncatesToByteArg) {
  const char* src =
      "module t;\n"
      "  int aa[shortint];\n"
      "  byte ix;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[300] = 1;\n"
      "    status = aa.first(ix);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);
  EXPECT_EQ(RunAndGet(src, "ix"), 300u & 0xFFu);  // 44
}

// A wider index type exercises the same rule at a larger scale: a longint index
// (64 bits) with an int argument (32 bits). The stored key exceeds 32 bits, so
// first() returns -1 and truncates to the low 32 bits.
TEST(AssocTraversalArgs, LongintIndexTruncatesToIntArg) {
  const char* src =
      "module t;\n"
      "  int aa[longint];\n"
      "  int k;\n"
      "  int status;\n"
      "  initial begin\n"
      "    aa[64'h1_0000_0005] = 1;\n"
      "    status = aa.first(k);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);
  EXPECT_EQ(RunAndGet(src, "k"), 5u);  // low 32 bits of 0x1_0000_0005
}

// The clause 7.9.4 worked pattern with a narrow argument driven end to end: a
// forward walk seeded by first() and stepped by next() still visits every entry
// even though each returned key is truncated into the byte argument. Using keys
// that are distinct in their low 8 bits keeps the traversal well defined; the
// sum of the values at the visited keys proves the full walk.
TEST(AssocTraversalArgs, NarrowArgStillWalksAllEntries) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  byte ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = 0;\n"
      "    found = aa.first(ix);\n"
      "    do result = result + aa[ix];\n"
      "    while (aa.next(ix));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
