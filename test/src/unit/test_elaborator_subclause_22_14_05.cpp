#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The word this version adds, in the role it exists for: it names a net type,
// and the net has to reach the elaborated design carrying that type. Every form
// of the declaration is here -- scalar, vector, signed -- because the width and
// the signedness travel by paths of their own. The same source under the later
// of the two lists this version includes cannot be elaborated at all, which is
// what makes the word an addition rather than something carried over.
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

  // Under "1364-2001" the word is an ordinary identifier, so `uwire
  // scalar_net;` is read as a module instantiation and the parser reports the
  // missing port connection list under §23.3.2. §22.14.5 itself states only
  // which words are reserved -- "This version includes the identifiers listed
  // in versions 1364-1995 (see Table 22-1) and 1364-2001 (see Table 22-2) plus
  // the additional identifiers listed in Table 22-3" -- and the keyword table
  // in src/lexer/keywords.cpp carries that out by choosing a token kind, which
  // files no diagnostic of its own.
  //
  // The line named here and in the cases below comes from LineInRegion in
  // lib/cpp/test_helpers/helpers_keyword_version.h rather than from a literal.
  // LineInRegion counts the lines In writes above the body, so a change to what
  // In writes moves every one of these cases at once. Its answer is the line of
  // the source as written, because the region's opening directive occupies one
  // line of preprocessed output and not two.
  ElabFixture earlier;
  ElaborateWithPreprocessorAllowingParseErrors(In2001("module m;\n"
                                                      "  uwire scalar_net;\n"
                                                      "endmodule\n"),
                                               earlier, "m");
  EXPECT_TRUE(ReportedError(earlier.diag.Diagnostics(), "expected '(', got ';'",
                            LineInRegion(2), "23.3.2"));
}

// The same net type on a module port, so the addition is observed across a
// hierarchy rather than inside one module: the child declares the port with the
// word this version adds, and the parent binds a net of that type to it.
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

// The declaration forms the two tests above do not reach, carried into the
// elaborated design. A net declaration may bring its own assignment along, and
// a port may be declared in the separate style where the header lists only
// names and the body supplies direction and type; each is a production of its
// own, and the net the added word opens has to reach the design from either.
// That the first form's assignment really drives the net is observed at the
// simulator stage; nets carry no driver list at this one.
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

// The other face of the same addition: being reserved here, the word cannot
// name a variable, and under both of the lists this version includes the very
// same declaration builds one. Reading the variable back off those designs is
// what keeps the accepting legs from being any elaboration that happens to
// succeed.
TEST(Verilog2005KeywordElaboration, AddedWordCannotNameAnElaboratedVariable) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

  // A reserved word cannot be the name in a variable declaration, so the report
  // is the one §6.8 governs: the declaration wanted an identifier and got a
  // keyword token.
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

// The line a report on a `begin_keywords region stands at, read on a
// declaration further down the region than the cases above put one. A
// diagnostic sends the user to a line of their own source, and a directive that
// wrote two lines of preprocessed output where the source had one would send
// them one line past it. Preprocessor::HandleBeginKeywords writes the keyword
// marker and the version byte alone, and RunPreprocLoop ends that line at
// src/preprocessor/preprocessor.cpp:611 as it ends every other line, so the
// declaration is reported on the line In wrote it, which LineInRegion(3) gives.
// Counting newlines in the preprocessed text does not show the offset reaching
// the user; this does.
TEST(Verilog2005KeywordElaboration, ReservedWordDeeperInARegionKeepsItsLine) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

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

// The second included list at this stage, swept whole. Each of Table 22-2's
// entries is reserved here, and under "1364-1995" -- the other list this
// version includes, where it is not yet a keyword -- the same declaration
// elaborates into a variable of the width it asked for. The pair is what makes
// each word an inclusion rather than an unrelated failure.
TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  EXPECT_EQ(std::size(kTable222Words), 21u);
  for (const char* word : kTable222Words) {
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

// The first included list, swept at this stage. There is no earlier version to
// pair these against -- they have been reserved since the list this version
// starts from -- so the accepting side of the claim is the test below, where
// the same words build the design in their keyword roles.
TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  EXPECT_EQ(std::size(kTable221), 102u);
  size_t swept = 0;
  for (const char* word : kTable221) {
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

// Table 22-1 doing its work under this version, read back as elaborated
// structure. The net types are the sharpest part: each resolved and driven type
// the earlier list names has to survive into the design as itself rather than
// collapsing onto a plain wire, which would leave the inclusion unobserved.
TEST(Verilog2005KeywordElaboration, IncludedVerilog1995WordsStillBuildDesign) {
  ExpectTable221DeclarationsElaborate("1364-2005");
}

// Table 22-2 doing its work, likewise as structure rather than as tokens.
// `localparam` resolves to a constant, `genvar`/`generate`/`endgenerate`
// produce one copy of the loop body per iteration, and `signed`/`unsigned`
// select what they select. The three are tied together on purpose: the
// localparam is the loop bound, so the count of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
TEST(Verilog2005KeywordElaboration, IncludedVerilog2001WordsStillBuildDesign) {
  ExpectTable222DeclarationsElaborate("1364-2005");
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required: a literal and a `parameter` come
// from Table 22-1, and `localparam` and the `automatic` that lets a constant
// function be written come from Table 22-2. So every one of them is writable
// here by virtue of what this version includes rather than of anything it adds,
// and the width the design ends up with is what shows the constant resolved.
//
// The remaining constant form, a genvar, shows its value only in the copies its
// loop produces rather than in a width, and it is observed doing exactly that
// in IncludedVerilog2001WordsStillBuildDesign above -- there against a loop
// bound that is itself a constant and with a nested condition singling out one
// iteration, which is strictly more than a copy count. Repeating a weaker
// version of it here would add nothing.
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

// The negative the three tables imply, carried to this stage. A word none of
// them lists is an ordinary identifier here, so it names an object that really
// reaches the design -- and it is not a data type, which is the half that would
// go unchecked if only the naming side were tested.
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

    // An unlisted word heads no data type here, so the declaration is read as a
    // plain variable named by the word and the packed dimension that follows is
    // where §6.8's variable declaration ends.
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
