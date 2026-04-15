// §23.3.1

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TopLevelModules, MultipleTopLevelModules) {
  auto r = Parse(
      "module top_a; endmodule\n"
      "module top_b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
}

TEST(TopLevelModules, SingleModuleParsesAsTopCandidate) {
  auto r = Parse("module only; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "only");
}

TEST(TopLevelModules, DollarRootHierPathInAssignParses) {
  EXPECT_TRUE(ParseOk(
      "module top;\n"
      "  logic x;\n"
      "  assign x = $root.top.x;\n"
      "endmodule\n"));
}

TEST(TopLevelModules, DollarRootHierPathInInitialBlockParses) {
  EXPECT_TRUE(ParseOk(
      "module top;\n"
      "  logic [7:0] val;\n"
      "  initial val = $root.top.val;\n"
      "endmodule\n"));
}

TEST(TopLevelModules, DollarRootMultiLevelHierPathParses) {
  EXPECT_TRUE(ParseOk(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic x;\n"
      "  assign x = $root.top.c1.sig;\n"
      "endmodule\n"));
}

}  // namespace
