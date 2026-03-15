// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilationUnitStructure, ConfigWithEndLabel) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(CompilationUnitStructure, PrimitiveWithEndLabel) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(CompilationUnitStructure, MissingEndconfigIsError) {
  EXPECT_FALSE(ParseOk(
      "module m; endmodule\n"
      "config c;\n"
      "  design m;"));
}

TEST(CompilationUnitStructure, MissingEndprimitiveIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"));
}

}  // namespace
