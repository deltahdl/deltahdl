#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(RunAndGet(src, "status"), 0xFFFFFFFFull);
  EXPECT_EQ(RunAndGet(src, "ix"), 232u);
}

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
  EXPECT_EQ(ix, 500u & 0xFFu);
}

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
  EXPECT_EQ(RunAndGet(src, "ix"), 300u & 0xFFu);
}

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
  EXPECT_EQ(RunAndGet(src, "ix"), 300u & 0xFFu);
}

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
  EXPECT_EQ(RunAndGet(src, "k"), 5u);
}

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
