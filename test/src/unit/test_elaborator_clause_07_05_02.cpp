#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DynamicArraySizeValidation, SizeCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int s;\n"
             "  initial s = d.size();\n"
             "endmodule\n"));
}

TEST(DynamicArraySizeValidation, SizeAfterNewElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = new[8];\n"
             "  int s;\n"
             "  initial s = d.size();\n"
             "endmodule\n"));
}

TEST(DynamicArraySizeValidation, SizeInExpressionElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = '{1, 2, 3};\n"
             "  int d2[];\n"
             "  initial d2 = new[d.size() * 2](d);\n"
             "endmodule\n"));
}

}  // namespace
