#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueSizeElaboration, QueueSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  int sz;\n"
             "  initial sz = q.size();\n"
             "endmodule\n"));
}

TEST(QueueSizeElaboration, QueueSizeNoParensOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  int sz;\n"
             "  initial sz = q.size;\n"
             "endmodule\n"));
}

}  // namespace
