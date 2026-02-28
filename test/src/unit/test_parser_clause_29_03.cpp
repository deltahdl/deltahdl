// §29.3: UDP definition

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: extern followed by full definition ---
TEST(ParserAnnexA051, ExternThenDefinition) {
  auto r = Parse(
      "extern primitive inv(output out, input in);\n"
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_TRUE(r.cu->udps[0]->table.empty());
  EXPECT_EQ(r.cu->udps[1]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->table.size(), 2u);
}

// --- udp_declaration: wildcard port with sequential ---
TEST(ParserAnnexA051, WildcardPortSequential) {
  auto r = Parse(
      "primitive dff(.*);\n"
      "  output reg q;\n"
      "  input d;\n"
      "  input clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
}

}  // namespace
