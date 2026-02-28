// §10.11: Net aliasing

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static ModuleItem* FindAlias(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlias) return item;
  }
  return nullptr;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

namespace {

// =============================================================================
// A.6.1 Production: net_alias (parsing)
// net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
// =============================================================================
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
  // §10.11: alias with bit-selects for byte-swapping
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
