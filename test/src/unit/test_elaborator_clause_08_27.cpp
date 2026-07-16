#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassObjectElaboration, ForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassWithoutForwardTypedefOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ForwardTypedefInterfaceClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, UnresolvedForwardTypedefClassError) {
  EXPECT_FALSE(
      ElabOk("typedef class C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.27: the bare `typedef C2;` form is equivalent to `typedef class C2;` and
// shall work the same way. Equivalence includes the resolution rule: an
// unresolved bare forward typedef must be rejected by the same production path
// that rejects the class-keyword form (see UnresolvedForwardTypedefClassError).
TEST(ClassObjectElaboration, UnresolvedBareForwardTypedefClassError) {
  EXPECT_FALSE(
      ElabOk("typedef C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ForwardTypedefParameterizedClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C;\n"
             "module top;\n"
             "  C#(1, real) v2;\n"
             "  C#(.p(2), .T(real)) v3;\n"
             "endmodule\n"
             "class C #(parameter p = 2, type T = int);\n"
             "endclass\n"));
}

TEST(ClassObjectElaboration, BareForwardTypedefWithoutClassKeywordOk) {
  EXPECT_TRUE(
      ElabOk("typedef C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
