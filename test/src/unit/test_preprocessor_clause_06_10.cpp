#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, ImplicitNetInPortList) {
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

TEST(ParserSection6, ImplicitNetInContAssign) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  assign out = in1 & in2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, ImplicitNetInModuleInst) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  sub u1(.a(w1), .b(w2));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, DefaultNettypeNoneRejectsImplicit) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module m;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

  EXPECT_FALSE(r.has_errors);
}

}  // namespace
