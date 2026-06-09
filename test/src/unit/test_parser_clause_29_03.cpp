#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §29.3: a UDP definition shall not appear between the module/program/
// interface/package keyword pairs. All four container bodies funnel their
// items through the single ParseModuleItem dispatch, which has no primitive
// case, so the rejection is applied at one production point regardless of the
// enclosing container. The module body stands in for all four here; the
// program/interface/package variants would only re-exercise the same path.
TEST(UdpTopLevelParsing, PrimitiveInsideModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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

}
