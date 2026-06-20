#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueDeleteElaboration, DeleteWithIndexElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial q.delete(0);\n"
             "endmodule\n"));
}

TEST(QueueDeleteElaboration, DeleteNoArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial q.delete();\n"
             "endmodule\n"));
}

TEST(QueueDeleteElaboration, DeletePropertyStyleElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial q.delete;\n"
             "endmodule\n"));
}

}  // namespace
