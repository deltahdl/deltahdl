#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;
namespace {

TEST(SpecifyBlockDeclParsing, PulsestyleAndShowcancelledTogether) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect out1;\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 2u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(spec->specify_items[1]->is_noshowcancelled);
}

TEST(SpecifyBlockDeclParsing, EmptySpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items.empty());
}

TEST(SpecifyBlockDeclParsing, PulsestyleOnevent) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(spec->specify_items[0]->is_ondetect);
}

TEST(SpecifyBlockDeclParsing, NoshowcancelledDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
}

TEST(SpecifyBlockDeclParsing, SpecparamAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tHL = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

TEST(SpecifyBlockDeclParsing, PathDeclarationAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
}

TEST(SpecifyBlockDeclParsing, SystemTimingCheckAsSpecifyItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge c, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kTimingCheck);
}

TEST(SpecifyBlockDeclParsing, PulsestyleListOfPathOutputsTakesDescriptors) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q[3], bus[7:0], \\q-1 , intf.p;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  const auto& outs = spec->specify_items[0]->path_outputs;
  ASSERT_EQ(outs.size(), 4u);
  EXPECT_EQ(outs[0].name, "q");
  EXPECT_EQ(outs[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(outs[1].name, "bus");
  EXPECT_EQ(outs[1].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(outs[2].name, "q-1");
  EXPECT_EQ(outs[3].interface_name, "intf");
  EXPECT_EQ(outs[3].name, "p");
}

TEST(SpecifyBlockDeclParsing, ShowcancelledListOfPathOutputsTakesDescriptors) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled q[0], \\q-1 ;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
  const auto& outs = spec->specify_items[0]->path_outputs;
  ASSERT_EQ(outs.size(), 2u);
  EXPECT_EQ(outs[0].name, "q");
  EXPECT_EQ(outs[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(outs[1].name, "q-1");
  EXPECT_EQ(outs[1].range_kind, SpecifyRangeKind::kNone);
}

TEST(SpecifyBlockDeclParsing, PulsestyleBraceListRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent {a, b};\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "path terminals are listed with commas alone; a "
                            "concatenation is no specify terminal",
                            3, "A.7.3"));
}

TEST(SpecifyBlockDeclParsing, PulsestyleDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.7.4.1"));
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

TEST(SpecifyBlockDeclParsing, ShowcancelledDeclMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.7.4.2"));
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
}

TEST(SpecifyBlockDeclParsing, SpecifyBlockMissingEndspecifyRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endspecify', got EOF", 3, "30.3"));
}

struct SpecifyItemRejection {
  const char* item;
  const char* message;
  const char* subclause;
};

void ExpectEachItemRejected(const std::vector<SpecifyItemRejection>& cases) {
  for (const auto& c : cases) {
    auto r = Parse(std::string("module m(input a, b, output q, y);\n"
                               "  specify\n"
                               "    ") +
                   c.item +
                   "\n"
                   "  endspecify\n"
                   "endmodule\n");
    uint32_t line =
        std::string_view(c.message).starts_with("expected ';'") ? 4 : 3;
    EXPECT_TRUE(ReportedError(r.diags, c.message, line, c.subclause)) << c.item;
  }
}

TEST(SpecifyBlockDeclParsing, APulsestyleOndetectNeedsAListAndASemicolon) {
  ExpectEachItemRejected({
      {"pulsestyle_ondetect ;", "expected identifier, got ';'", "30.4"},
      {"pulsestyle_ondetect q", "expected ';', got 'endspecify'", "30.7.4.1"},
      {"pulsestyle_ondetect {q, y};", "a concatenation is no specify terminal",
       "A.7.3"},
  });
  EXPECT_TRUE(
      ParseOk("module m(input a, output q, y);\n"
              "  specify\n"
              "    pulsestyle_ondetect q, y;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(SpecifyBlockDeclParsing,
     AShowcancelledDeclarationNeedsAListAndASemicolon) {
  ExpectEachItemRejected({
      {"showcancelled ;", "expected identifier, got ';'", "30.4"},
      {"noshowcancelled ;", "expected identifier, got ';'", "30.4"},
      {"showcancelled {q, y};", "a concatenation is no specify terminal",
       "A.7.3"},
      {"noshowcancelled {q, y};", "a concatenation is no specify terminal",
       "A.7.3"},
      {"noshowcancelled q", "expected ';', got 'endspecify'", "30.7.4.2"},
  });
  EXPECT_TRUE(
      ParseOk("module m(input a, output q, y);\n"
              "  specify\n"
              "    showcancelled q, y;\n"
              "    noshowcancelled q, y;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(SpecifyBlockDeclParsing, ASystemTaskOtherThanATimingCheckIsNoSpecifyItem) {
  ExpectEachItemRejected({
      {"$finish;", "system task cannot appear in specify block", "31.2"},
      {"$foo(a, b);", "system task cannot appear in specify block", "31.2"},
  });
  EXPECT_TRUE(
      ParseOk("module m(input a, b, output q);\n"
              "  specify\n"
              "    $setup(a, posedge b, 1);\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(SpecifyBlockDeclParsing, AModuleItemThatIsNoSpecifyItemIsRejected) {
  ExpectEachItemRejected({
      {"wire w;", "unexpected token in specify block", "30.3"},
      {"specify endspecify", "unexpected token in specify block", "30.3"},
      {"assign q = a;", "unexpected token in specify block", "30.3"},
      {"and g(q, a, b);", "unexpected token in specify block", "30.3"},
  });
  EXPECT_TRUE(
      ParseOk("module m(input a, b, output q);\n"
              "  wire w;\n"
              "  specify\n"
              "    specparam w_delay = 2;\n"
              "  endspecify\n"
              "  specify endspecify\n"
              "  assign q = a;\n"
              "endmodule\n"));
}

}  // namespace
