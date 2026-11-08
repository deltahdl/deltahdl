#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueAssignElaboration, ConcatAppendOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {q, 6};\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, ConcatPrependOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int e;\n"
             "  initial q = {e, q};\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, BareSliceOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[1:$];\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, BareSliceToDollarMinusOneOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[0:$-1];\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, ConcatWithVariableBoundSlicesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int e, pos;\n"
             "  initial q = {q[0:pos-1], e, q[pos:$]};\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, BareSliceDroppingFirstTwoOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[2:$];\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, BareSliceDroppingFirstAndLastOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[1:$-1];\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, NonblockingConcatAppendOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q <= {q, 6};\n"
             "endmodule\n"));
}

TEST(QueueAssignElaboration, NonblockingBareSliceOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q <= q[1:$];\n"
             "endmodule\n"));
}

}  // namespace
