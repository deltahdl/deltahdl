#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueOpsElaboration, SliceWithVariableBoundsOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int dst[$];\n"
             "  int a, b;\n"
             "  initial dst = {q[a:b]};\n"
             "endmodule\n"));
}

TEST(QueueOpsElaboration, SliceWithDollarBoundOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int dst[$];\n"
             "  initial dst = {q[0:$]};\n"
             "endmodule\n"));
}

TEST(QueueOpsElaboration, IndexedWriteOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q[0] = 42;\n"
             "endmodule\n"));
}

TEST(QueueOpsElaboration, EmptyConcatClearOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {};\n"
             "endmodule\n"));
}

}  // namespace
