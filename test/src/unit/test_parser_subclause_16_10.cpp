#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(LocalVariableParsing, AssertionVariableDeclInSequenceParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

TEST(LocalVariableParsing, MatchItemsOfAGroupJoiningSequencesAreKept) {
  for (const char* op : {"or", "and", "intersect", "within"}) {
    SCOPED_TRACE(op);
    auto r = Parse(std::string("module m;\n"
                               "  sequence s;\n"
                               "    int x;\n"
                               "    @(posedge clk) (a ") +
                   op +
                   " b, x = 1) ##1 (x == 1);\n"
                   "  endsequence\n"
                   "endmodule\n");
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
    ASSERT_NE(item, nullptr);
    const SeqLinearBody& body = item->seq_linear;
    ASSERT_EQ(body.operands.size(), 2u);
    ASSERT_EQ(body.match_items[0].size(), 1u);
    EXPECT_EQ(body.match_items[0][0].lvar, "x");
    EXPECT_TRUE(body.match_items[1].empty());
  }
}

TEST(LocalVariableParsing, AssertionVariableDeclMultipleNames) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic u, v = a, w = v || b;\n"
      "    @(posedge clk) (a, u = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 3u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "u");
  EXPECT_EQ(item->prop_seq_assert_vars[1], "v");
  EXPECT_EQ(item->prop_seq_assert_vars[2], "w");
}

TEST(LocalVariableParsing, SequenceWithBothLocalKindsRecordedSeparately) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout int v1);\n"
      "    bit guard;\n"
      "    @(posedge clk) (a, guard = 1'b1) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "guard");
}

TEST(LocalVariableParsing, AssertionVariableDeclInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int x;\n"
      "    @(posedge clk) (valid_in, x = pipe_in) |-> ##5 (pipe_out1 == "
      "(x+1));\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

TEST(LocalVariableParsing, NoAssertionVariableMeansEmptyList) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->prop_seq_assert_vars.empty());
}

TEST(LocalVariableParsing, AssertionVariableDeclWithPackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    bit [7:0] q;\n"
      "    @(posedge clk) (a, q = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "q");
}

TEST(LocalVariableParsing, LocalVariableInClockingEventIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge x) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "local variable \"x\" may not be used in a clocking event expression", 4,
      "16.10"));
}

TEST(LocalVariableParsing, LocalVariableNotInClockingEventParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

TEST(LocalVariableParsing, AssertionVariableDeclWithSigning) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic signed x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

TEST(LocalVariableParsing, AssertionVariableDeclWithConstantInitializer) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x = 0;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

TEST(LocalVariableParsing, MultipleAssertionVariableDeclLinesAccumulate) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    logic y;\n"
      "    bit z;\n"
      "    @(posedge clk) (a, x = data, y = 1'b1, z = 1'b0) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 3u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
  EXPECT_EQ(item->prop_seq_assert_vars[1], "y");
  EXPECT_EQ(item->prop_seq_assert_vars[2], "z");
}

TEST(LocalVariableParsing, AChandleLocalVariableIsReported) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a;\n"
      "  sequence s; int n; chandle h; @(posedge clk) a; endsequence\n"
      "  property p; chandle h; @(posedge clk) a; endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  constexpr char kMessage[] =
      "an assertion variable may not be declared of type chandle";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "16.10"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "16.10"));
}

TEST(SequenceLocalVariableParsing,
     AGroupsItemsAfterARepeatedOperandStandApart) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s1; int x; @(posedge clk) a ##1 (b[*2], x++); endsequence\n"
      "  sequence s2; int x; @(posedge clk) a ##1 (b[->2], x++); endsequence\n"
      "  sequence s3; int x; @(posedge clk) a ##1 (b, x++); endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kSequenceDecl) continue;
    SCOPED_TRACE(item->name);
    const SeqLinearBody& body = item->seq_linear;
    const bool kFused = item->name != "s3";
    ASSERT_EQ(body.operands.size(), kFused ? 3u : 2u);
    EXPECT_EQ(body.match_items[1].size(), kFused ? 0u : 1u);
    if (!kFused) continue;
    EXPECT_EQ(body.match_items[2].size(), 1u);
    EXPECT_EQ(body.operands[2]->text, "1");
    EXPECT_EQ(body.delays[2].min, 0u);
    EXPECT_EQ(body.delays[2].max, 0u);
    EXPECT_EQ(body.repetitions[2].kind, SeqRepetition::Kind::kNone);
  }
}

TEST(SequenceLocalVariableParsing, AMatchItemTargetMaySelectWithinTheLocal) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    logic [7:0] v;\n"
      "    pair_t p;\n"
      "    @(posedge clk) (a, v[1] = b, p.hi += 2, ++v[3:2], p.lo[0]--, v = 0)"
      " ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  const SeqLinearBody& body = item->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  const std::vector<SeqMatchAssign>& items = body.match_items[0];
  struct Case {
    std::string_view lvar;
    TokenKind op;
    ExprKind target;
  };
  const Case kCases[] = {{"v", TokenKind::kEq, ExprKind::kSelect},
                         {"p", TokenKind::kPlusEq, ExprKind::kMemberAccess},
                         {"v", TokenKind::kPlusEq, ExprKind::kSelect},
                         {"p", TokenKind::kMinusEq, ExprKind::kSelect}};
  ASSERT_EQ(items.size(), 5u);
  for (size_t i = 0; i < 4; ++i) {
    SCOPED_TRACE(i);
    EXPECT_EQ(items[i].lvar, kCases[i].lvar);
    EXPECT_EQ(items[i].op, kCases[i].op);
    ASSERT_NE(items[i].target, nullptr);
    EXPECT_EQ(items[i].target->kind, kCases[i].target);
  }
  EXPECT_EQ(items[4].lvar, "v");
  EXPECT_EQ(items[4].target, nullptr);
}

struct LocalClockCase {
  const char* decl;
  int line;
};

const LocalClockCase kLocalClockCases[] = {
    {"module m;\n"
     "  property p; logic x; @(posedge x) (a, x = b) |-> c; endproperty\n"
     "endmodule\n",
     2},
    {"module m;\n"
     "  sequence s; logic x; @(x) (a, x = b) ##1 c; endsequence\n"
     "endmodule\n",
     2},
    {"module m;\n"
     "  sequence s; logic x; @(posedge clk iff x) (a, x = b) ##1 c;\n"
     "  endsequence\n"
     "endmodule\n",
     2},
    {"module m;\n"
     "  sequence s; logic x;\n"
     "    @(posedge clk) (a, x = b) ##1 @(posedge x) c;\n"
     "  endsequence\n"
     "endmodule\n",
     3},
    {"module m;\n"
     "  property p; logic x;\n"
     "    @(posedge clk) (a, x = b) |=> @(negedge x) c;\n"
     "  endproperty\n"
     "endmodule\n",
     3},
    {"module m;\n"
     "  sequence s(local input logic x); @(posedge x) a ##1 c; endsequence\n"
     "endmodule\n",
     2},
    {"interface i;\n"
     "  sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n"
     "endinterface\n",
     2},
    {"program pr;\n"
     "  sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n"
     "endprogram\n",
     2},
    {"checker ck;\n"
     "  sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n"
     "endchecker\n",
     2},
    {"package pk;\n"
     "  sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n"
     "endpackage\n",
     2},
    {"module m;\n"
     "  if (1) begin : g\n"
     "    sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n"
     "  end\n"
     "endmodule\n",
     3},
    {"sequence s; logic x; @(posedge x) (a, x = b) ##1 c; endsequence\n", 1},
};

TEST(LocalVariableParsing, ALocalInAnyClockingEventIsReported) {
  for (const auto& c : kLocalClockCases) {
    auto r = Parse(c.decl);
    EXPECT_TRUE(ReportedError(
        r.diags,
        "local variable \"x\" may not be used in a clocking event expression",
        c.line, "16.10"))
        << c.decl;
  }
}

TEST(LocalVariableParsing, ALocalBesideTheClockingEventIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  sequence s; logic x; @(posedge clk iff en) (a, x = b) ##1 x;\n"
      "  endsequence\n"
      "  property p; logic x;\n"
      "    @(posedge clk) (a, x = b) |=> @(negedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

constexpr const char* kImplicitType =
    "an assertion variable shall be declared with an explicit data type";

std::string Filled(const char* text, const std::string& decl) {
  std::string out = text;
  for (size_t at = out.find("@@"); at != std::string::npos;
       at = out.find("@@", at + decl.size())) {
    out.replace(at, 2, decl);
  }
  return out;
}

struct DeclPlace {
  const char* text;
  int sequence_line;
  int property_line;
};

constexpr const char* kModuleBodies =
    "module m;\n"
    "  logic clk, a;\n"
    "  sequence s; @@ @(posedge clk) a; endsequence\n"
    "  property p; @@ @(posedge clk) a; endproperty\n"
    "endmodule\n";

const DeclPlace kDeclPlaces[] = {
    {kModuleBodies, 3, 4},
    {"interface i;\n"
     "  logic clk, a;\n"
     "  sequence s; @@ @(posedge clk) a; endsequence\n"
     "  property p; @@ @(posedge clk) a; endproperty\n"
     "endinterface\n",
     3, 4},
    {"program pr;\n"
     "  logic clk, a;\n"
     "  sequence s; @@ @(posedge clk) a; endsequence\n"
     "  property p; @@ @(posedge clk) a; endproperty\n"
     "endprogram\n",
     3, 4},
    {"checker ck(logic clk, logic a);\n"
     "  sequence s; @@ @(posedge clk) a; endsequence\n"
     "  property p; @@ @(posedge clk) a; endproperty\n"
     "endchecker\n",
     2, 3},
    {"package pk;\n"
     "  sequence s; @@ @(posedge 1'b1) 1'b1; endsequence\n"
     "  property p; @@ @(posedge 1'b1) 1'b1; endproperty\n"
     "endpackage\n",
     2, 3},
    {"module m;\n"
     "  logic clk, a;\n"
     "  if (1) begin : g\n"
     "    sequence s; @@ @(posedge clk) a; endsequence\n"
     "    property p; @@ @(posedge clk) a; endproperty\n"
     "  end\n"
     "endmodule\n",
     4, 5},
    {"module m;\n"
     "  logic clk, a;\n"
     "  clocking cb @(posedge clk);\n"
     "    sequence s; @@ a; endsequence\n"
     "    property p; @@ a; endproperty\n"
     "  endclocking\n"
     "endmodule\n",
     4, 5},
    {"sequence s; @@ @(posedge 1'b1) 1'b1; endsequence\n"
     "property p; @@ @(posedge 1'b1) 1'b1; endproperty\n",
     1, 2},
};

struct ImplicitPair {
  const char* implicit;
  const char* explicit_type;
};

const ImplicitPair kImplicitPairs[] = {
    {"var v;", "var logic v;"},
    {"var signed v;", "var logic signed v;"},
    {"var unsigned v;", "var bit unsigned v;"},
    {"var [3:0] v;", "var logic [3:0] v;"},
    {"var [1:0][3:0] v;", "var logic [1:0][3:0] v;"},
    {"var signed [3:0] v;", "var logic signed [3:0] v;"},
    {"var v = 1;", "var logic v = 1;"},
    {"var signed [3:0] v = 2;", "var logic signed [3:0] v = 2;"},
    {"var [3:0] v, u = 1;", "var logic [3:0] v, u = 1;"},
    {"int n; var v;", "int n; var logic v;"},
};

TEST(AssertionVariableType, DISABLED_AnImplicitTypeAfterVarIsReported) {
  for (const ImplicitPair& pair : kImplicitPairs) {
    SCOPED_TRACE(pair.implicit);
    auto r = Parse(Filled(kModuleBodies, pair.implicit));
    EXPECT_TRUE(ReportedError(r.diags, kImplicitType, 3, "16.10"));
    EXPECT_TRUE(ReportedError(r.diags, kImplicitType, 4, "16.10"));
  }
}

TEST(AssertionVariableType, TheNearestExplicitTypeAfterVarIsAccepted) {
  for (const ImplicitPair& pair : kImplicitPairs) {
    SCOPED_TRACE(pair.explicit_type);
    auto r = Parse(Filled(kModuleBodies, pair.explicit_type));
    EXPECT_FALSE(r.has_errors);
  }
}

TEST(AssertionVariableType, DISABLED_AnImplicitTypeIsReportedInEveryPlace) {
  for (const DeclPlace& place : kDeclPlaces) {
    SCOPED_TRACE(place.text);
    auto r = Parse(Filled(place.text, "var v;"));
    EXPECT_TRUE(
        ReportedError(r.diags, kImplicitType, place.sequence_line, "16.10"));
    EXPECT_TRUE(
        ReportedError(r.diags, kImplicitType, place.property_line, "16.10"));
  }
}

TEST(AssertionVariableType, AnExplicitTypeIsAcceptedInEveryPlace) {
  for (const DeclPlace& place : kDeclPlaces) {
    SCOPED_TRACE(place.text);
    auto r = Parse(Filled(place.text, "var logic v;"));
    EXPECT_FALSE(r.has_errors);
  }
}

const ImplicitPair kWithoutVarPairs[] = {
    {"signed [3:0] v;", "logic signed [3:0] v;"},
    {"[3:0] v;", "logic [3:0] v;"},
    {"signed v;", "logic signed v;"},
};

TEST(AssertionVariableType, AnImplicitTypeWithoutVarIsNotADeclaration) {
  for (const ImplicitPair& pair : kWithoutVarPairs) {
    SCOPED_TRACE(pair.implicit);
    auto r = Parse(Filled(kModuleBodies, pair.implicit));
    constexpr char kNotAdmitted[] =
        "this declaration's body is not one the grammar admits";
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, 3, "A.2.10"));
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, 4, "A.2.10"));
  }
}

TEST(AssertionVariableType, AnExplicitTypeWithoutVarIsAccepted) {
  for (const ImplicitPair& pair : kWithoutVarPairs) {
    SCOPED_TRACE(pair.explicit_type);
    auto r = Parse(Filled(kModuleBodies, pair.explicit_type));
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
