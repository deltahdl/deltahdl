#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueInsertElaboration, InsertElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial q.insert(0, 42);\n"
             "endmodule\n"));
}

TEST(QueueInsertElaboration, InsertWithVariableIndex) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  integer idx;\n"
             "  initial begin\n"
             "    idx = 1;\n"
             "    q.insert(idx, 99);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
