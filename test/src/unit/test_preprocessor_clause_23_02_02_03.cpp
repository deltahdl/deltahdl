// §23.2.2.3: Rules for determining port kind, data type, and direction

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.2.1.2 Port declarations
// =============================================================================
// --- inout_declaration ---
// inout net_port_type list_of_port_identifiers
TEST(ParserA212, InoutWireNetType) {
  auto r = ParseWithPreprocessor("module m(inout wire a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "a");
}

}  // namespace
