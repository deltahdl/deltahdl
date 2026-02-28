// Annex A.4.1.2: Interface instantiation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- interface_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0412, MultipleInterfaceInstances) {
  auto r = Parse("module m; my_if u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

}  // namespace
