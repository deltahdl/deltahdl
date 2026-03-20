#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UdpBodyPreprocessor, CombinationalBodyThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive and_udp(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, SequentialBodyThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, MacroExpandedInitVal) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define INIT_VAL 1'b0\n"
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = `INIT_VAL;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, ConditionalCompilationInTable) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define FULL_TABLE\n"
      "primitive mux(output y, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "`ifdef FULL_TABLE\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "`endif\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, EdgeSymbolsThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive edge_det(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, ParenthesizedEdgeThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 (01) : ? : 0;\n"
      "    1 (01) : ? : 1;\n"
      "    ? (10) : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, AllLevelSymbolsThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "    x : 0;\n"
      "    X : 0;\n"
      "    ? : 0;\n"
      "    b : 0;\n"
      "    B : 0;\n"
      "  endtable\n"
      "endprimitive\n"));
}

TEST(UdpBodyPreprocessor, AllInitValFormsThroughPreprocessor) {
  for (const char* init_val :
       {"1'b0", "1'b1", "1'bx", "1'bX", "1'B0", "1'B1", "1'Bx", "1'BX", "0",
        "1"}) {
    std::string src =
        "primitive p(output reg q, input d, clk);\n"
        "  initial q = " +
        std::string(init_val) +
        ";\n"
        "  table\n"
        "    0 r : ? : 0;\n"
        "  endtable\n"
        "endprimitive\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(src)) << "init_val: " << init_val;
  }
}

}  // namespace
