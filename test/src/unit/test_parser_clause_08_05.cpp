#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ObjectPropertyParsing, PropertyAccessDotNotation) {
  auto r = Parse(
      "class Packet;\n"
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
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules.back();
  ASSERT_NE(mod, nullptr);

  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "Packet");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->name, "command");
  EXPECT_EQ(cls->members[1]->name, "address");
}

TEST(ObjectPropertyParsing, ParameterizedClassWithValueParam) {
  auto r = Parse(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "vector");
  ASSERT_GE(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "width");
}

TEST(ObjectPropertyParsing, ParameterAccessViaInstance) {
  ParseOk(
      "class vector #(parameter width = 7, type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    w = v.width;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectPropertyParsing, EnumAccessViaInstance) {
  ParseOk(
      "class Packet;\n"
      "  typedef enum {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    automatic int x;\n"
      "    p = new;\n"
      "    x = p.ERR_OVERFLOW;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectPropertyParsing, PropertyReadAndWrite) {
  ParseOk(
      "class Packet;\n"
      "  bit [3:0] command;\n"
      "  bit [40:0] address;\n"
      "  integer time_requested;\n"
      "  const integer buffer_size = 100;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    automatic int var1;\n"
      "    automatic integer packet_time;\n"
      "    p = new;\n"
      "    p.command = 4'd0;\n"
      "    p.address = 41'b0;\n"
      "    packet_time = p.time_requested;\n"
      "    var1 = p.buffer_size;\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
