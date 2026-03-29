#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(InterfaceClassTypeAccess, InterfaceClassWithTypedef) {
  auto r = Parse(
      "interface class ihello;\n"
      "  typedef int int_t;\n"
      "  pure virtual function void hello(int_t val);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "ihello");
}

TEST(InterfaceClassTypeAccess, ScopeResolutionOnInterfaceClassType) {
  auto r = Parse(
      "interface class IntfC;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function t1_t funcC();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    IntfC::t1_t x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionOnInterfaceClassParam) {
  auto r = Parse(
      "interface class IC;\n"
      "  parameter int SIZE = 64;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = IC::SIZE;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionOnParameterizedInterfaceClass) {
  auto r = Parse(
      "interface class IntfA #(type T1 = logic);\n"
      "  typedef T1[1:0] T2;\n"
      "  pure virtual function T2 funcA();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    IntfA#(bit)::T2 val;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionEnumValueAccess) {
  auto r = Parse(
      "interface class IntfC;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function t1_t funcC();\n"
      "endclass\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = IntfC::ONE;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(InterfaceClassTypeAccess, TypedefWithParameterInInterfaceClass) {
  auto r = Parse(
      "interface class IC;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  pure virtual function data_t read();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

}  // namespace
