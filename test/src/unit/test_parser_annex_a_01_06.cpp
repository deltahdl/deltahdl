// Annex A.1.6: Interface items

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// Combined: interface with multiple A.1.6 item types.
TEST(SourceText, InterfaceMultipleItemTypes) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  extern function void validate();\n"
      "  extern forkjoin task run_parallel();\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  // data var + extern function + extern forkjoin task = 3 items
  ASSERT_GE(ifc->items.size(), 3u);
  EXPECT_EQ(ifc->modports.size(), 2u);
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kFunctionDecl, "validate"));
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kTaskDecl, "run_parallel"));
}

}  // namespace
