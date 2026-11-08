#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  ElabOk(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
}

TEST(ClassObjectElaboration, UnresolvedBareForwardTypedefClassError) {
  ElabFixture f;
  ElabOk(
      "typedef C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
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

TEST(ClassObjectElaboration, ForwardDeclaredClassIsRecordedWithNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "typedef logic [7:0] byte_t;\n"
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  byte_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto width_of = [design](std::string_view name) -> int64_t {
    auto it = design->type_widths.find(name);
    if (it == design->type_widths.end()) return -1;
    return it->second;
  };
  EXPECT_EQ(width_of("byte_t"), 8);
  EXPECT_EQ(width_of("C"), 0);
}

}  // namespace
