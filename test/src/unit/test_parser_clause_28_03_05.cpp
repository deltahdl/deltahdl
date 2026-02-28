// §28.3.5: The range specification

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] )
// name_of_instance ::= instance_identifier { unpacked_dimension }
// =============================================================================
TEST(ParserAnnexA0411, InstanceArrayWithRange) {
  // instance_identifier [ left : right ]
  auto r = Parse("module m; sub u0[3:0](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- interface_instantiation: with instance array ---
TEST(ParserAnnexA0412, InterfaceInstArray) {
  auto r = Parse("module m; my_if u0 [3:0] (.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

}  // namespace
