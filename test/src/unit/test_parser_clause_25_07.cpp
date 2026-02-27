// §25.7: Tasks and functions in interfaces

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA29, ImportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

}  // namespace
