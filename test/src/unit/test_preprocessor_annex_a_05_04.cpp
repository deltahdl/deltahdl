#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UdpInstantiationPreprocessor, BasicInstantiationThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv u1(y, a);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, UnnamedInstanceThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (y, a);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, WithDriveStrengthThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (strong0, weak1) u1(y, a);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, WithDelayThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv #(3, 5) u1(y, a);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, MacroExpandedDelay) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define RISE 3\n"
      "`define FALL 5\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv #(`RISE, `FALL) u1(y, a);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, MultipleInstancesThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  inv u1(y1, a), u2(y2, b);\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, ConditionalCompilationAroundInstance) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define USE_UDP\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "`ifdef USE_UDP\n"
      "  inv u1(y, a);\n"
      "`endif\n"
      "endmodule\n"));
}

TEST(UdpInstantiationPreprocessor, StrengthAndDelayThroughPreprocessor) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  inv (pull0, pull1) #10 u1(y, a);\n"
      "endmodule\n"));
}

}  // namespace
