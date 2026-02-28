// Non-LRM tests

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// { attribute_instance } on port declarations
// ---------------------------------------------------------------------------
// Attribute on output declaration
TEST(ParserAnnexA052, AttrOnOutputDecl) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  (* synthesis = \"off\" *) output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
}

}  // namespace
