#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;
static ModuleItem* FindAlias(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlias) return item;
  }
  return nullptr;
}
namespace {

TEST(ParserA601, NetAlias_TwoNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

TEST(ParserA601, NetAlias_ThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 3u);
}

TEST(ParserA601, NetAlias_FourNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b = c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 4u);
}

TEST(ParserA601, NetAlias_BitSelect) {
  auto r = Parse(
      "module m;\n"
      "  wire [31:0] A, B;\n"
      "  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindAlias(r.cu->modules[0]->items);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

}  // namespace
