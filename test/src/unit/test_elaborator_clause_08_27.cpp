#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.27: Forward typedef class followed by class definition — OK.
TEST(ElabA827, ForwardTypedefClassOk) {
  EXPECT_TRUE(ElabOk(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "class C2;\n"
      "  C1 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.27: Single class with no forward typedef — OK.
TEST(ElabA827, ClassWithoutForwardTypedefOk) {
  EXPECT_TRUE(ElabOk(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.27: Forward typedef interface class — OK.
TEST(ElabA827, ForwardTypedefInterfaceClassOk) {
  EXPECT_TRUE(ElabOk(
      "typedef interface class IC;\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
