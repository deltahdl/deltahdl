

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(PortDeclaration, StructAsPortType) {
  EXPECT_TRUE(ParseOk(
      "module inner(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } data_in,\n"
      "  output logic [15:0] data_out\n"
      ");\n"
      "  assign data_out = data_in;\n"
      "endmodule\n"));
}

TEST(PortDeclaration, UnionAsPortType) {
  EXPECT_TRUE(ParseOk(
      "module m(\n"
      "  input union packed { logic [31:0] word; logic [3:0][7:0] bytes; } u\n"
      ");\n"
      "endmodule\n"));
}

TEST(PortDeclaration, EventAsPortType) {
  auto r = Parse("module m(input event e); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kEvent);
}

TEST(PortDeclaration, TypedefStructWithUnionAsPortType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {\n"
              "    bit isfloat;\n"
              "    union { int i; shortreal f; } n;\n"
              "  } tagged_st;\n"
              "endmodule\n"
              "module mh1(\n"
              "  input var int in1,\n"
              "  input var shortreal in2,\n"
              "  output tagged_st out\n"
              ");\n"
              "endmodule\n"));
}

TEST(PortDeclaration, InterfaceAsPortType) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module m(ifc bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_TRUE(mod->ports[0].is_interface_port);
}

TEST(PortDeclaration, ArrayAsPortType) {
  auto r = Parse(
      "module m(\n"
      "  input logic [7:0] mem [0:15],\n"
      "  output wire [3:0] bus [4]\n"
      ");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "mem");
  EXPECT_FALSE(mod->ports[0].unpacked_dims.empty());
  EXPECT_EQ(mod->ports[1].name, "bus");
  EXPECT_FALSE(mod->ports[1].unpacked_dims.empty());
}

TEST(PortDeclaration, ModuleWithAtLeast256Ports) {
  std::string src = "module wide(";
  const int port_count = 300;
  for (int i = 0; i < port_count; ++i) {
    if (i > 0) src += ", ";
    src += "input logic p";
    src += std::to_string(i);
  }
  src += ");\nendmodule\n";
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), static_cast<size_t>(port_count));
}

TEST(PortDeclaration, ModuleWithExactly256Ports) {
  std::string src = "module wide(";
  const int port_count = 256;
  for (int i = 0; i < port_count; ++i) {
    if (i > 0) src += ", ";
    src += "input logic p";
    src += std::to_string(i);
  }
  src += ");\nendmodule\n";
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), static_cast<size_t>(port_count));
}

TEST(PortDeclaration, UnpackedArrayOfStructAsPortType) {
  auto r = Parse(
      "module m(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } items [0:3]\n"
      ");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "items");
  EXPECT_EQ(mod->ports[0].data_type.kind, DataTypeKind::kStruct);
  EXPECT_FALSE(mod->ports[0].unpacked_dims.empty());
}

}  // namespace
