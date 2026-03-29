#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ClassParsing, ParameterizedClass) {
  auto r = Parse(
      "class stack #(parameter int DEPTH = 8);\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "stack");
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "DEPTH");
}

TEST(ClassParsing, ParameterizedClassMultipleParams) {
  auto r = Parse(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "WIDTH");
  EXPECT_EQ(cls->params[1].first, "DEPTH");
}

TEST(ClassParsing, ParameterizedClassTypeParam) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

TEST(ClassParsing, ParameterizedClassExtendsName) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  EXPECT_EQ(cls->name, "Derived");
  EXPECT_EQ(cls->base_class, "Base");
  EXPECT_TRUE(cls->base_class_type_params.empty());
}

TEST(ClassParsing, ParameterizedClassExtendsParams) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "N");
}

TEST(ClassParsing, ParameterizedClassInsideModuleName) {
  auto r = Parse(
      "module class_tb;\n"
      "  class test_cls #(parameter a = 12);\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  EXPECT_EQ(cls->name, "test_cls");
}

TEST(ClassParsing, ParameterizedClassInsideModuleParams) {
  auto r = Parse(
      "module class_tb;\n"
      "  class test_cls #(parameter a = 12);\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  ASSERT_NE(cls->class_decl, nullptr);
  ASSERT_EQ(cls->class_decl->params.size(), 1u);
  EXPECT_EQ(cls->class_decl->params[0].first, "a");
}

TEST(ParameterizedClassParsing, MultipleParamsWithDefaults) {
  auto r = Parse(
      "virtual class Codec#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = $clog2(IN_W));\n"
      "  static function logic [OUT_W-1:0] encode(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    encode = '0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->params[0].first, "IN_W");
  EXPECT_EQ(r.cu->classes[0]->params[1].first, "OUT_W");
}

TEST(ParameterizedClassParsing, ThreeParams) {
  auto r = Parse(
      "virtual class Xform#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = IN_W * 2,\n"
      "                     parameter DEPTH = 4);\n"
      "  static function logic [OUT_W-1:0] widen(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    return {DEPTH{data}};\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 3u);
}

TEST(ParameterizedClassParsing, NoDefaultParam) {
  auto r = Parse(
      "virtual class Shifter#(parameter int AMOUNT);\n"
      "  static function logic [31:0] left(input logic [31:0] val);\n"
      "    return val << AMOUNT;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 1u);
}

TEST(ParameterizedClassParsing, ClassExtends) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  virtual function void display();\n"
              "  endfunction\n"
              "endclass\n"
              "virtual class Derived#(parameter N = 1) extends Base;\n"
              "  static function int count();\n"
              "    return N;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ClassParsing, ParameterizedClassSpecialization) {
  auto r = Parse(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "endclass\n"
      "module m;\n"
      "  vector #(10) vten;\n"
      "  vector #(.size(2)) vtwo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassParsing, ParameterizedClassStackType) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "  function void push(T a);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

TEST(ClassParsing, ParameterizedClassDefaultInstantiation) {
  auto r = Parse(
      "class stack #(type T = int);\n"
      "  T items[];\n"
      "endclass\n"
      "module m;\n"
      "  stack is_default;\n"
      "  stack #(real) rs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassParsing, TypeParameterClassMember) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T value;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

TEST(ParameterizedClassParsing, ClassWithParams) {
  auto r = Parse("class C #(type T = int); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// §8.25: typedef to avoid repeating specialization.
TEST(ParameterizedClassParsing, TypedefSpecialization) {
  EXPECT_TRUE(
      ParseOk("class vector #(int size = 1);\n"
              "  bit [size-1:0] a;\n"
              "endclass\n"
              "typedef vector#(4) Vfour;\n"));
}

// §8.25: typedef chain — typedef of typedef specialization.
TEST(ParameterizedClassParsing, TypedefChainedSpecialization) {
  EXPECT_TRUE(
      ParseOk("class stack #(type T = int);\n"
              "  T items[];\n"
              "endclass\n"
              "typedef stack#(real) RealStack;\n"
              "module m;\n"
              "  RealStack s;\n"
              "endmodule\n"));
}

// §8.25: Extending a parameterized base class with explicit #(...) params.
TEST(ParameterizedClassParsing, ExtendsParameterizedBase) {
  auto r = Parse(
      "class C #(type T = bit);\n"
      "  T data;\n"
      "endclass\n"
      "class D #(type P = real) extends C #(integer);\n"
      "  P extra;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* d = r.cu->classes[1];
  EXPECT_EQ(d->name, "D");
  EXPECT_EQ(d->base_class, "C");
  ASSERT_EQ(d->base_class_type_params.size(), 1u);
  EXPECT_EQ(d->base_class_type_params[0].type_name, "integer");
}

// §8.25: Forwarding type parameter to parameterized base class.
TEST(ParameterizedClassParsing, ExtendsBaseForwardingTypeParam) {
  auto r = Parse(
      "class C #(type T = bit);\n"
      "  T data;\n"
      "endclass\n"
      "class D #(type P = real) extends C #(P);\n"
      "  P extra;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* d = r.cu->classes[1];
  EXPECT_EQ(d->base_class, "C");
  ASSERT_EQ(d->base_class_type_params.size(), 1u);
  EXPECT_EQ(d->base_class_type_params[0].type_name, "P");
}

// §8.25: Type parameter used as base class.
TEST(ParameterizedClassParsing, TypeParamAsBaseClass) {
  EXPECT_TRUE(
      ParseOk("class C #(type T = bit);\n"
              "endclass\n"
              "class D #(type P = C#(real)) extends P;\n"
              "endclass\n"));
}

// §8.25: Mixed type and value parameters.
TEST(ParameterizedClassParsing, MixedTypeAndValueParams) {
  auto r = Parse(
      "class C #(type T = int, parameter int N = 8);\n"
      "  T data;\n"
      "  bit [N-1:0] flags;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "T");
  EXPECT_EQ(cls->params[1].first, "N");
  EXPECT_TRUE(cls->type_param_names.count("T"));
  EXPECT_FALSE(cls->type_param_names.count("N"));
}

// §8.25: Explicit default specialization C#() syntax.
TEST(ParameterizedClassParsing, ExplicitDefaultSpecialization) {
  EXPECT_TRUE(
      ParseOk("class C #(int p = 1);\n"
              "endclass\n"
              "module m;\n"
              "  C #() obj;\n"
              "endmodule\n"));
}

// §8.25: User-defined type (struct) as type parameter default.
TEST(ParameterizedClassParsing, StructAsTypeParamDefault) {
  EXPECT_TRUE(
      ParseOk("typedef struct { int x; int y; } point_t;\n"
              "class container #(type T = point_t);\n"
              "  T value;\n"
              "endclass\n"));
}

// §8.25: Class as type parameter argument.
TEST(ParameterizedClassParsing, ClassAsTypeParamArg) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  int data;\n"
              "endclass\n"
              "class stack #(type T = int);\n"
              "  T items[];\n"
              "endclass\n"
              "module m;\n"
              "  stack #(Packet) ps;\n"
              "endmodule\n"));
}

// §8.25: Instantiation with bit-vector type specialization.
TEST(ParameterizedClassParsing, BitVectorTypeSpecialization) {
  EXPECT_TRUE(
      ParseOk("class stack #(type T = int);\n"
              "  T items[];\n"
              "endclass\n"
              "module m;\n"
              "  stack#(bit[1:10]) bs;\n"
              "endmodule\n"));
}

// §8.25: Static member declared inside parameterized class.
TEST(ParameterizedClassParsing, StaticMemberInParameterizedClass) {
  auto r = Parse(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "  static int count = 0;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 2u);
}

}  // namespace
