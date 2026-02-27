// §25.5: Modports

#include "fixture_parser.h"

using namespace delta;

namespace {

// §A.2.9 modport_declaration ::= modport modport_item { , modport_item } ;
TEST(ParserA29, BasicModportDecl) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  modport target(input a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "target");
}

}  // namespace
