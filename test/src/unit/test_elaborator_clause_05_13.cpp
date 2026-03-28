#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, ArraySizeMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  int s;\n"
             "  initial s = arr.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  int s;\n"
             "  initial s = arr.size;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, QueuePushBackOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial begin\n"
             "    q.push_back(42);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, DynArraySizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, StringLenOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  int n;\n"
             "  initial n = s.len();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, EnumNumOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodWithDefaultArgNoParensOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  color_e n;\n"
             "  initial n = c.next;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodNoParensInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  int r;\n"
             "  initial r = arr.size + 1;\n"
             "endmodule\n"));
}

}  // namespace
