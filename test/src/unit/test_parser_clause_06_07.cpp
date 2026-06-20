#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NetDeclarationSyntax, BuiltinNetTypeAlternative) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
}

TEST(NetDeclarationSyntax, EachNetTypeKeywordRecognized) {
  auto r = Parse(
      "module m;\n"
      "  supply0 a;\n"
      "  supply1 b;\n"
      "  tri c;\n"
      "  triand d;\n"
      "  trior e;\n"
      "  trireg f;\n"
      "  tri0 g;\n"
      "  tri1 h;\n"
      "  uwire i;\n"
      "  wire j;\n"
      "  wand k;\n"
      "  wor l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 12u);
  for (auto* it : items) {
    EXPECT_EQ(it->kind, ModuleItemKind::kNetDecl);
    EXPECT_TRUE(it->data_type.is_net);
  }
}

TEST(NetDeclarationSyntax, NettypeIdentifierAlternative) {
  auto r = Parse(
      "module m;\n"
      "  nettype logic [7:0] myNet;\n"
      "  myNet n;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetDeclarationSyntax, InterconnectAlternative) {
  auto r = Parse(
      "module m;\n"
      "  interconnect ic;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_interconnect);
}

TEST(NetDeclarationSyntax, InterconnectWithUnpackedDim) {
  auto r = Parse(
      "module m;\n"
      "  interconnect [3:0] ic [1:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetDeclarationSyntax, InterconnectWithSingleDelayValue) {
  auto r = Parse(
      "module m;\n"
      "  interconnect #5 ic;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->data_type.is_interconnect);
}

TEST(NetDeclarationSyntax, InterconnectMultipleIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "  interconnect ic1, ic2, ic3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "ic1");
  EXPECT_EQ(items[1]->name, "ic2");
  EXPECT_EQ(items[2]->name, "ic3");
  for (auto* it : items) {
    EXPECT_TRUE(it->data_type.is_interconnect);
  }
}

TEST(DriveStrengthSyntax, Strength0ThenStrength1) {
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, strong1) w = 1'b1; endmodule\n"));
}

TEST(DriveStrengthSyntax, Strength1ThenStrength0) {
  EXPECT_TRUE(
      ParseOk("module m; wire (strong1, strong0) w = 1'b1; endmodule\n"));
}

TEST(DriveStrengthSyntax, Strength0ThenHighz1) {
  EXPECT_TRUE(ParseOk("module m; wire (pull0, highz1) w = 1'b1; endmodule\n"));
}

TEST(DriveStrengthSyntax, Strength1ThenHighz0) {
  EXPECT_TRUE(ParseOk("module m; wire (weak1, highz0) w = 1'b1; endmodule\n"));
}

TEST(DriveStrengthSyntax, Highz0ThenStrength1) {
  EXPECT_TRUE(
      ParseOk("module m; wire (highz0, supply1) w = 1'b1; endmodule\n"));
}

TEST(DriveStrengthSyntax, Highz1ThenStrength0) {
  EXPECT_TRUE(
      ParseOk("module m; wire (highz1, supply0) w = 1'b1; endmodule\n"));
}

TEST(Strength0Keywords, EachKeyword) {
  EXPECT_TRUE(
      ParseOk("module m; wire (supply0, strong1) w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, strong1) w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (pull0,   strong1) w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (weak0,   strong1) w = 1'b1; endmodule\n"));
}

TEST(Strength1Keywords, EachKeyword) {
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, supply1) w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, strong1) w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, pull1)   w = 1'b1; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m; wire (strong0, weak1)   w = 1'b1; endmodule\n"));
}

TEST(ChargeStrengthSyntax, NonTriregKeywordRejectsChargeStrength) {
  EXPECT_FALSE(ParseOk("module m; wire (small) w; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; tri (medium) w; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; wand (large) w; endmodule\n"));
  EXPECT_FALSE(ParseOk("module m; supply0 (small) w; endmodule\n"));
}

TEST(ChargeStrengthSyntax, SmallMediumLarge) {
  {
    auto r = Parse("module m; trireg (small) t; endmodule\n");
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.charge_strength,
              static_cast<uint8_t>(1));
  }
  {
    auto r = Parse("module m; trireg (medium) t; endmodule\n");
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.charge_strength,
              static_cast<uint8_t>(2));
  }
  {
    auto r = Parse("module m; trireg (large) t; endmodule\n");
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.charge_strength,
              static_cast<uint8_t>(4));
  }
}

TEST(NetDelay3Form, SingleDelayValue) {
  auto r = Parse("module m; wire #5 w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
  EXPECT_NE(r.cu->modules[0]->items[0]->net_delay, nullptr);
}

TEST(NetDelay3Form, TwoDelayMinTypMax) {
  auto r = Parse("module m; wire #(1, 2) w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
  EXPECT_NE(r.cu->modules[0]->items[0]->net_delay, nullptr);
  EXPECT_NE(r.cu->modules[0]->items[0]->net_delay_fall, nullptr);
}

TEST(NetDelay3Form, ThreeDelayMinTypMax) {
  auto r = Parse("module m; trireg (small) #(1, 2, 3) t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
  EXPECT_NE(r.cu->modules[0]->items[0]->net_delay_decay, nullptr);
}

TEST(NetDelay3Form, SingleMintypmaxInParens) {
  auto r = Parse("module m; wire #(4) w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
  EXPECT_NE(r.cu->modules[0]->items[0]->net_delay, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->net_delay_fall, nullptr);
}

TEST(NetDelayValueForm, UnsignedNumberAndRealNumber) {
  EXPECT_TRUE(ParseOk("module m; wire #7 a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; wire #3.14 a; endmodule\n"));
}

TEST(NetDelayValueForm, OneStepLiteral) {
  EXPECT_TRUE(ParseOk("module m; wire #1step a; endmodule\n"));
}

TEST(NetDelayValueForm, PsIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  parameter delay_p = 5;\n"
      "  wire #delay_p w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetDelayValueForm, TimeLiteral) {
  auto r = Parse(
      "module m;\n"
      "  wire #5ns w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ListOfNetDeclAssignments, MultipleAssignmentsInOneDecl) {
  auto r = Parse("module m; wire a, b, c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
}

TEST(NetDeclAssignmentForm, IdentifierWithUnpackedDimension) {
  auto r = Parse("module m; wire w [0:7]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->unpacked_dims.size(), 1u);
}

TEST(NetDeclAssignmentForm, IdentifierWithInitExpression) {
  auto r = Parse("module m; wire w = 1'b0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_NE(items[0]->init_expr, nullptr);
}

}  // namespace
