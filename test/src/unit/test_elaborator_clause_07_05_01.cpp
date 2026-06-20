#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewValidation, NewSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  initial d = new[10];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, NewSizeWithInitElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int src[] = '{1, 2, 3};\n"
             "  initial d = new[5](src);\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, NewZeroSizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  initial d = new[0];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, DeclWithNewElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = new[4];\n"
             "endmodule\n"));
}

TEST(DynamicArrayNewValidation, SelfReferenceResizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = '{1, 2, 3};\n"
             "  initial d = new[6](d);\n"
             "endmodule\n"));
}

}  // namespace
