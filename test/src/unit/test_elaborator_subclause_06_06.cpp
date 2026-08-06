#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NetTypes, AllBuiltinNetTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  tri tr;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  triand ta;\n"
      "  trior to_;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  trireg tg;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  uwire uw;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 12u);

  auto find_net = [&](std::string_view name) -> const RtlirNet* {
    for (const auto& n : mod->nets) {
      if (n.name == name) return &n;
    }
    return nullptr;
  };

  auto* n = find_net("w");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWire);

  n = find_net("tr");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTri);

  n = find_net("wa");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWand);

  n = find_net("wo");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kWor);

  n = find_net("ta");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTriand);

  n = find_net("to_");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTrior);

  n = find_net("t0");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTri0);

  n = find_net("t1");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTri1);

  n = find_net("tg");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kTrireg);

  n = find_net("s0");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kSupply0);

  n = find_net("s1");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kSupply1);

  n = find_net("uw");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
}

TEST(NetTypes, BuiltinNetsAreNotMarkedAsUserDefined) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  tri tr;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  triand ta;\n"
      "  trior to_;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  trireg tg;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  uwire uw;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 12u);
  for (const auto& n : mod->nets) {
    EXPECT_FALSE(n.is_user_nettype)
        << "built-in net '" << n.name << "' must not be user-defined";
    EXPECT_TRUE(n.nettype_name.empty())
        << "built-in net '" << n.name << "' must carry no nettype identifier";
  }
}

TEST(NetTypes, UserDefinedNettypeIsDistinguishedFromBuiltin) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic my_net;\n"
      "  wire w;\n"
      "  my_net u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 2u);

  const RtlirNet* builtin = nullptr;
  const RtlirNet* user = nullptr;
  for (const auto& n : mod->nets) {
    if (n.name == "w") builtin = &n;
    if (n.name == "u") user = &n;
  }
  ASSERT_NE(builtin, nullptr);
  ASSERT_NE(user, nullptr);
  EXPECT_FALSE(builtin->is_user_nettype);
  EXPECT_TRUE(user->is_user_nettype);
}

}  // namespace
