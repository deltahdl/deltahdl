#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, ForwardTypedefClassMutualReferencePreprocessor) {
  auto r = ParseWithPreprocessor(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "class C2;\n"
      "  C1 c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "C1");
  EXPECT_EQ(r.cu->classes[1]->name, "C2");
}

TEST(ClassParsing, ForwardTypedefInterfaceClassPreprocessor) {
  auto r = ParseWithPreprocessor(
      "typedef interface class IC;\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

TEST(ClassParsing, ForwardTypedefParameterizedClassPreprocessor) {
  auto r = ParseWithPreprocessor(
      "typedef class C;\n"
      "module top;\n"
      "  C#(1, real) v2;\n"
      "endmodule\n"
      "class C #(parameter p = 2, type T = int);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
}

}  // namespace
