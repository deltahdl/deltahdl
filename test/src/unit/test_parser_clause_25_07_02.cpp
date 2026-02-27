// §25.7.2: Example of using tasks in modports

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA29, ImportThenDirectionPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(import Read, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].name, "data");
}

}  // namespace
