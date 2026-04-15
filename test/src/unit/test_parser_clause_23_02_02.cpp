

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
  EXPECT_TRUE(ParseOk(
      "module m;\n"
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

}  // namespace
