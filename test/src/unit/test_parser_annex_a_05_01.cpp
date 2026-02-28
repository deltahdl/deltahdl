// Annex A.5.1: UDP declaration

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: endprimitive with end label ---
TEST(ParserAnnexA051, EndLabel) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
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

// Helper: verify parsed extern UDP named "inv" with one input.
static void VerifyExternInvPrimitive(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "inv");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "in");
  EXPECT_TRUE(udp->table.empty());
}

// --- udp_declaration: extern udp_ansi_declaration ---
TEST(ParserAnnexA051, ExternAnsi) {
  auto r = Parse("extern primitive inv(output out, input in);\n");
  VerifyExternInvPrimitive(r);
}

// --- udp_declaration: extern udp_nonansi_declaration ---
TEST(ParserAnnexA051, ExternNonAnsi) {
  auto r = Parse("extern primitive inv(out, in);\n");
  VerifyExternInvPrimitive(r);
}

}  // namespace
