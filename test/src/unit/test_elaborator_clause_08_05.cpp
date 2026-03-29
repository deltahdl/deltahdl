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

TEST(ObjectPropertyElaboration, PropertyAccessElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p.command = 1;\n"
             "  end\n"
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

TEST(ObjectPropertyElaboration, TypeParamAccessViaHandleIsIllegal) {
  EXPECT_FALSE(
      ElabOk("class vector #(parameter width = 7, type T = int);\n"
             "  T data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    vector #(3) v;\n"
             "    v = new;\n"
             "    $display((v.T)'(3));\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
