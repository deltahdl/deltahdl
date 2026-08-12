#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ObjectPropertyElaboration, ClassWithPropertiesElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, VariousPropertyTypes) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int i;\n"
             "  real r;\n"
             "  string s;\n"
             "  bit [7:0] b;\n"
             "  logic [31:0] l;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, MultiplePropertyAccess) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int header;\n"
             "  int payload;\n"
             "  int crc;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    p.header = 1;\n"
             "    p.payload = 2;\n"
             "    p.crc = 3;\n"
             "    x = p.header;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, PropertyReadElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic int var1;\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.command = 1;\n"
             "    p.address = 2;\n"
             "    var1 = p.command;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, EnumAccessViaInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  typedef enum {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} "
             "PCKT_TYPE;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    automatic int x;\n"
             "    p = new;\n"
             "    x = p.ERR_OVERFLOW;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, ParameterValueAccessViaInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class vector #(parameter width = 7, type T = int);\n"
             "  T data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic int w;\n"
             "    vector #(3) v;\n"
             "    v = new;\n"
             "    w = v.width;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.5 states "Accessing data types using a class handle is not allowed" and
// gives `$display ((v.T)'(3.45));` as its illegal example.
TEST(ObjectPropertyElaboration, TypeParamAccessViaHandleIsIllegal) {
  ElabFixture f;
  ElabOk(
      "class vector #(parameter width = 7, type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    $display((v.T)'(3));\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "cannot access type parameter via class handle");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "8.5");
}

// §8.5 says of a parameter value read through an instance name "Such an
// expression is not a constant expression". The rule that rejects the source is
// §11.5.1's, which requires the width of an indexed part-select to be a
// constant expression, so the report names §11.5.1 rather than §8.5.
TEST(ObjectPropertyElaboration, InstanceParamAccessIsNotConstant) {
  ElabFixture f;
  ElabOk(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n"
      "module m;\n"
      "  logic [31:0] bus;\n"
      "  logic [31:0] slice;\n"
      "  initial begin\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    slice = bus[0 +: v.width];\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "indexed part-select width must be a constant expression");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "11.5.1");
}

// The same part-select with a literal constant width is legal, isolating the
// rejection above to the non-constant instance-qualified access.
TEST(ObjectPropertyElaboration, ConstantPartSelectWidthOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [31:0] bus;\n"
             "  logic [3:0] slice;\n"
             "  initial begin\n"
             "    slice = bus[0 +: 4];\n"
             "  end\n"
             "endmodule\n"));
}

// §8.5: accessing a data type through a class handle is illegal, but naming a
// type through the class scope resolution operator on a specialization is legal
// typecasting - the accepting counterpart to TypeParamAccessViaHandleIsIllegal.
TEST(ObjectPropertyElaboration, TypeAccessViaScopeResolutionIsLegal) {
  EXPECT_TRUE(
      ElabOk("class vector #(parameter width = 7, type T = int);\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    $display(vector#(3)::T'(3));\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
