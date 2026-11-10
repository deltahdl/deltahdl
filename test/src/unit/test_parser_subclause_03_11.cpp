#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrimitiveIsALeaf, PrimitiveHoldingOnlyItsTableIsAccepted) {
  auto r = Parse(
      "primitive pass_through(output o, input i);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(PrimitiveIsALeaf, ModuleInstanceInsideAPrimitiveIsReported) {
  auto r = Parse(
      "module leaf; endmodule\n"
      "primitive holder(output o, input i);\n"
      "  leaf l();\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'table', got identifier", 3, "29.3.4"));
}

TEST(PrimitiveIsALeaf, GateInstanceInsideAPrimitiveIsReported) {
  auto r = Parse(
      "primitive holder(output o, input i);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "  and g(o, i, i);\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprimitive', got 'and'", 6, "29.3"));
}

}  // namespace
