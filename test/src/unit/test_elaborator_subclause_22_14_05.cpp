#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {
TEST(Verilog2005KeywordElaboration, AddedWordBuildsNetsOfItsOwnType) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(In2005("module m;\n"
                                       "  uwire              scalar_net;\n"
                                       "  uwire [7:0]        vector_net;\n"
                                       "  uwire signed [7:0] signed_net;\n"
                                       "endmodule\n"),
                                f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "scalar_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 1u);

  n = FindNet(design, "m", "vector_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);

  n = FindNet(design, "m", "signed_net");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_TRUE(n->is_signed);

  ElabFixture earlier;
  ElaborateWithPreprocessor(In2001("module m;\n"
                                   "  uwire scalar_net;\n"
                                   "endmodule\n"),
                            earlier, "m");
  EXPECT_TRUE(ReportedError(earlier.diag.Diagnostics(),
                            "declaration of type 'uwire' does not precede this "
                            "reference to it",
                            LineInRegion(2), "6.18"));
}

TEST(Verilog2005KeywordElaboration, AddedWordTypesAPortAcrossAHierarchy) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2005("module child (input wire [7:0] a, output uwire [7:0] y);\n"
             "  assign y = a;\n"
             "endmodule\n"
             "module top;\n"
             "  wire  [7:0] src;\n"
             "  uwire [7:0] dst;\n"
             "  child u1 (.a(src), .y(dst));\n"
             "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* c = FindModule(design, "child");
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->ports.size(), 2u);
  EXPECT_EQ(c->ports[1].name, "y");
  EXPECT_EQ(c->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(c->ports[1].type_kind, DataTypeKind::kUwire);
  EXPECT_EQ(c->ports[1].width, 8u);

  const auto* n = FindNet(design, "top", "dst");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kUwire);
  EXPECT_EQ(n->width, 8u);
}

TEST(Verilog2005KeywordElaboration, AddedWordTypesEveryDeclarationForm) {
  ElabFixture with_assignment;
  auto* design =
      ElaborateWithPreprocessor(In2005("module m;\n"
                                       "  reg   [7:0] src;\n"
                                       "  uwire [7:0] bus = src + 8'd1;\n"
                                       "endmodule\n"),
                                with_assignment, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(with_assignment.has_errors);
  const auto* bus = FindNet(design, "m", "bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(bus->net_type, NetType::kUwire);
  EXPECT_EQ(bus->width, 8u);

  ElabFixture non_ansi;
  design = ElaborateWithPreprocessor(In2005("module ch (a, y);\n"
                                            "  input  [7:0] a;\n"
                                            "  output [7:0] y;\n"
                                            "  uwire  [7:0] y;\n"
                                            "  assign y = a;\n"
                                            "endmodule\n"),
                                     non_ansi, "ch");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  const auto* m = FindModule(design, "ch");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  const auto* y = FindNet(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->net_type, NetType::kUwire);
  EXPECT_EQ(y->width, 8u);
}

TEST(Verilog2005KeywordElaboration, AddedWordCannotNameAnElaboratedVariable) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* added = kVerilog2005AddedKeywords[0];

  ElabFixture reserved;
  ElaborateWithPreprocessorAllowingParseErrors(In2005(VarDecl(added)), reserved,
                                               "m");
  EXPECT_TRUE(
      ReportedError(reserved.diag.Diagnostics(),
                    std::string("expected identifier, got '") + added + "'",
                    LineInRegion(2), "6.8"));

  for (const auto& earlier : {In2001(VarDecl(added)), In1995(VarDecl(added))}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(earlier, f, "m");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const auto* v = FindVar(design, "m", added);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->width, 8u);
  }
}

TEST(Verilog2005KeywordElaboration, ReservedWordDeeperInARegionKeepsItsLine) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* added = kVerilog2005AddedKeywords[0];

  ElabFixture f;
  ElaborateWithPreprocessorAllowingParseErrors(
      In2005(std::string("module m;\n"
                         "  reg [7:0] first;\n"
                         "  reg [7:0] ") +
             added + ";\nendmodule\n"),
      f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    std::string("expected identifier, got '") + added + "'",
                    LineInRegion(3), "6.8"));
}

TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* word : kVerilog2001AddedKeywords) {
    ElabFixture reserved;
    ElaborateWithPreprocessorAllowingParseErrors(In2005(VarDecl(word)),
                                                 reserved, "m");
    EXPECT_TRUE(
        ReportedError(reserved.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
        << word;

    ElabFixture freed;
    auto* design = ElaborateWithPreprocessor(In1995(VarDecl(word)), freed, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  size_t swept = 0;
  for (const char* word : kVerilog1995Keywords) {
    if (IsGatePrimitiveWord(word)) continue;
    ElabFixture f;
    ElaborateWithPreprocessorAllowingParseErrors(In2005(VarDecl(word)), f, "m");
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
        << word << " is included from Table 22-1 and stays reserved";
    ++swept;
  }
  EXPECT_EQ(swept, 96u);
}

TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsStillBuildDesign) {
  ExpectVerilog1995DeclarationsElaborate("1364-2005");
}

TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsStillBuildDesign) {
  ExpectVerilog2001DeclarationsElaborate("1364-2005");
}

TEST(Verilog2005KeywordElaboration, EveryConstantFormResolvesUnderThisVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In2005("module t;\n"
             "  parameter  P = 8;\n"
             "  localparam L = 8;\n"
             "  function automatic integer width_of(input reg [7:0] n);\n"
             "    width_of = n;\n"
             "  endfunction\n"
             "  reg [7:0]            from_literal;\n"
             "  reg [P-1:0]          from_parameter;\n"
             "  reg [L-1:0]          from_localparam;\n"
             "  reg [width_of(8)-1:0] from_function;\n"
             "endmodule\n"),
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const char* const kNames[] = {"from_literal", "from_parameter",
                                "from_localparam", "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

TEST(Verilog2005KeywordElaboration, UnlistedWordsNameObjectsButAreNotTypes) {
  const char* const kUnlisted[] = {"logic", "interface", "bit", "byte", "int"};
  for (const char* word : kUnlisted) {
    ElabFixture named;
    auto* design = ElaborateWithPreprocessor(In2005(VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessorAllowingParseErrors(
        In2005(std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n"),
        as_type, "m");
    EXPECT_TRUE(ReportedError(as_type.diag.Diagnostics(),
                              "expected ';', got '['", LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace
