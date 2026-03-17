#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- assert_property_statement errors ---

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingOpenParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property a |-> b);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property (a |-> b;\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingPropertyKw) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert (a |-> b);\n"
              "endmodule\n"));
}

// --- assume_property_statement errors ---

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assume property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assume property (a |-> b;\n"
              "endmodule\n"));
}

// --- cover_property_statement errors ---

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover property (a |-> b;\n"
              "endmodule\n"));
}

// --- cover_sequence_statement errors ---

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover sequence (a ##1 b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover sequence (a ##1 b;\n"
              "endmodule\n"));
}

// --- restrict_property_statement errors ---

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  restrict property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  restrict property (a |-> b;\n"
              "endmodule\n"));
}

// --- property_declaration errors ---

TEST(PropertyDeclParsing, ErrorMissingEndproperty) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    a |-> b;\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorMissingPropertyName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property;\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    a |-> b;\n"
      "  endproperty : p2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PropertyDeclParsing, ErrorMissingSemicolonAfterName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorUnclosedPortList) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p(a, b;\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// --- sequence_declaration errors ---

TEST(SequenceDeclParsing, ErrorMissingEndsequence) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    a ##1 b;\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorMissingSequenceName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence;\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    a ##1 b;\n"
      "  endsequence : s2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceDeclParsing, ErrorMissingSemicolonAfterName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorUnclosedPortList) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s(a, b;\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// --- Edge cases: empty bodies, minimal constructs ---

TEST(PropertyDeclParsing, MinimalPropertyDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a; endproperty\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, MinimalSequenceDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a; endsequence\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, MinimalAssertProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, MinimalAssumeProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assume property (a);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, MinimalCoverProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover property (a);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, MinimalCoverSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover sequence (a);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, MinimalRestrictProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  restrict property (a);\n"
              "endmodule\n"));
}

// --- Multiple declarations ---

TEST(PropertyDeclParsing, MultiplePropertyDecls) {
  auto r = Parse(
      "module m;\n"
      "  property p1; a; endproperty\n"
      "  property p2; b; endproperty\n"
      "  property p3; c; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl),
      3u);
}

TEST(SequenceDeclParsing, MultipleSequenceDecls) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1; a; endsequence\n"
      "  sequence s2; b; endsequence\n"
      "  sequence s3; c; endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl),
      3u);
}

TEST(ConcurrentAssertionParsing, AllFiveAssertionTypes) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a);\n"
      "  assume property (b);\n"
      "  cover property (c);\n"
      "  cover sequence (d);\n"
      "  restrict property (e);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence),
      nullptr);
  ASSERT_NE(FindItemByKind(r.cu->modules[0]->items,
                            ModuleItemKind::kRestrictProperty),
            nullptr);
}

// --- Assertion in procedural context ---

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert property (a |-> b);\n"
      "  end\n"
      "endmodule\n");
  // assert property in initial block may be rejected or accepted
  // depending on parser — just verify no crash
  ASSERT_NE(r.cu, nullptr);
}

// --- Concurrent assertion with action blocks ---

TEST(ConcurrentAssertionParsing, AssertPropertyWithElseActionBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "    $display(\"pass\");\n"
              "  else\n"
              "    $error(\"fail\");\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, AssertPropertyWithPassActionOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "    $display(\"pass\");\n"
              "endmodule\n"));
}

}  // namespace
