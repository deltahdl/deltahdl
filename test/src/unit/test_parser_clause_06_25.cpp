#include "fixture_parser.h"

using namespace delta;

namespace {

// §6.25: Virtual class with type and value parameters defining typedefs.
TEST(ParserSection6, ParameterizedDataType_VirtualClassDef) {
  auto r = Parse(
      "virtual class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "  typedef logic [SIZE-1:0] t_vector;\n"
      "  typedef T t_array [SIZE-1:0];\n"
      "  typedef struct {\n"
      "    t_vector m0 [2*SIZE-1:0];\n"
      "    t_array m1;\n"
      "  } t_struct;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_TRUE(cls->is_virtual);
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "T");
  EXPECT_EQ(cls->params[1].first, "SIZE");
}

// §6.25: Specialization via scope resolution operator (::).
TEST(ParserSection6, ParameterizedDataType_ScopeResolution) {
  EXPECT_TRUE(ParseOk(
      "virtual class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "  typedef logic [SIZE-1:0] t_vector;\n"
      "endclass\n"
      "module top;\n"
      "  typedef logic [7:0] t_t0;\n"
      "  C#(t_t0, 3)::t_vector v0;\n"
      "endmodule\n"));
}

// §6.25: Multiple specializations of the same parameterized class.
TEST(ParserSection6, ParameterizedDataType_MultipleSpecializations) {
  EXPECT_TRUE(ParseOk(
      "virtual class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "  typedef T t_array [SIZE-1:0];\n"
      "  typedef struct {\n"
      "    T m0;\n"
      "  } t_struct;\n"
      "endclass\n"
      "module top;\n"
      "  typedef logic [7:0] t_t0;\n"
      "  C#(t_t0, 3)::t_vector v0;\n"
      "  C#(t_t0, 3)::t_array a0;\n"
      "  C#(bit, 4)::t_struct s0;\n"
      "endmodule\n"));
}

// §6.25: Parameterized class with single type parameter, default used.
TEST(ParserSection6, ParameterizedDataType_DefaultTypeParam) {
  EXPECT_TRUE(
      ParseOk("class container #(type T = int);\n"
              "  typedef T elem_t;\n"
              "endclass\n"
              "module m;\n"
              "  container::elem_t x;\n"
              "endmodule\n"));
}

// §6.25: Class with only value parameters for data type definition.
TEST(ParserSection6, ParameterizedDataType_ValueParamOnly) {
  EXPECT_TRUE(
      ParseOk("virtual class bus_def #(parameter WIDTH = 8);\n"
              "  typedef logic [WIDTH-1:0] data_t;\n"
              "endclass\n"
              "module m;\n"
              "  bus_def#(16)::data_t wide_bus;\n"
              "  bus_def#(8)::data_t narrow_bus;\n"
              "endmodule\n"));
}

}  // namespace
