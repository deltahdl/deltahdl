// §non-lrm:modport

#include "fixture_parser.h"

using namespace delta;

namespace {

// Empty modport (no ports) should parse
TEST(ParserA29, EmptyModport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport empty();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->ports.size(), 0u);
  EXPECT_EQ(mp->name, "empty");
}

}  // namespace
