#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(WeakReferenceStdPackageParser, ParameterizedDeclarationOfBuiltInType) {
  auto r = Parse(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  weak_reference #(my_obj) wr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(WeakReferenceStdPackageParser, PrototypeInstanceMethodsParse) {
  auto r = Parse(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_obj strong_obj;\n"
      "  my_obj result;\n"
      "  weak_reference #(my_obj) wr;\n"
      "  initial begin\n"
      "    strong_obj = new();\n"
      "    wr = new(strong_obj);\n"
      "    result = wr.get();\n"
      "    wr.clear();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(WeakReferenceStdPackageParser, StaticGetIdScopeResolutionParses) {
  auto r = Parse(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_obj o;\n"
      "  longint id;\n"
      "  initial begin\n"
      "    o = new();\n"
      "    id = weak_reference#(my_obj)::get_id(o);\n"
      "    if (weak_reference#(my_obj)::get_id(o) != 0) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(WeakReferenceStdPackageParser, WeakReferenceAsSubroutineFormalType) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  function void f(weak_reference #(my_obj) wr);\n"
              "    wr.clear();\n"
              "  endfunction\n"
              "endmodule\n"));
}

}  // namespace
