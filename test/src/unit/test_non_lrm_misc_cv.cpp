// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

using ProgramParseTest = ProgramTestParse;

namespace {

// Program with non-ANSI ports.
TEST(SourceText, ProgramNonAnsiHeader) {
  auto r = Parse(
      "program prg(clk);\n"
      "  input clk;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

// Program with wildcard ports: program p(.*);
TEST(SourceText, ProgramWildcardPorts) {
  auto r = Parse("program prg(.*); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_wildcard_ports);
}

}  // namespace
