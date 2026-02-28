// §28.3: Gate and switch declaration syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_CmosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(o1, i1, n1, p1), c2(o2, i2, n2, p2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "c1");
  EXPECT_EQ(gates[1]->gate_inst_name, "c2");
}

TEST(ParserA301, GateInst_MosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(o1, i1, c1), p2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(ParserA301, GateInst_EnableMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(o1, i1, c1), b2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(ParserA301, GateInst_NInputMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
}

}  // namespace
