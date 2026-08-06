#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ImplicitDeclaration, ImplicitNetInPortList) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ImplicitDeclaration, ImplicitNetInContAssign) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  assign out = in1 & in2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ImplicitDeclaration, ImplicitNetInModuleInst) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  sub u1(.a(w1), .b(w2));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ImplicitDeclaration, DefaultNettypeNoneRejectsImplicit) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module m;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

  EXPECT_FALSE(r.has_errors);
}

}  // namespace
