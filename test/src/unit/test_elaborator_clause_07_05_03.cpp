#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DynamicArrayDeleteValidation, DeleteCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[] = '{1, 2, 3};\n"
             "  initial d.delete();\n"
             "endmodule\n"));
}

TEST(DynamicArrayDeleteValidation, DeleteOnUninitializedElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  initial d.delete();\n"
             "endmodule\n"));
}

}  // namespace
