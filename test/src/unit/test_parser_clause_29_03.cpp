#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// A UDP definition placed inside a module body is not a legal module item;
// the parser should not consume it silently.
TEST(UdpTopLevelParsing, PrimitiveInsideModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveInsideProgramRejected) {
  auto r = Parse(
      "program p;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveInsideInterfaceRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveInsidePackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endpackage\n");
  EXPECT_TRUE(r.has_errors);
}

// A UDP definition placed between modules is at top level and must parse
// cleanly regardless of surrounding design-element order.
TEST(UdpTopLevelParsing, PrimitiveBetweenModulesAccepted) {
  auto r = Parse(
      "module a; endmodule\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// A UDP defined after a module that instantiates it is still a valid
// top-level design element; the parser must accept the source text.
TEST(UdpTopLevelParsing, PrimitiveDefinedAfterInstantiationSiteParses) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp u1(y, a);\n"
      "endmodule\n"
      "primitive my_udp(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// Implementations must accept at least 256 UDPs in a single model. Emit
// enough distinct UDPs to prove the parser and compilation-unit storage do
// not impose a small fixed cap.
TEST(UdpTopLevelParsing, AtLeast256UdpsAccepted) {
  std::string src;
  src.reserve(256 * 96);
  for (int i = 0; i < 300; ++i) {
    src += "primitive p";
    src += std::to_string(i);
    src += "(output out, input in);\n  table 0 : 1; 1 : 0; endtable\nendprimitive\n";
  }
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 300u);
}

}  // namespace
