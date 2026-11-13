#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(SequenceDeclarationInClockingBlockParsing, ClockingItemSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

TEST(SequenceDeclarationParsing, SequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s1");
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclCapturesFormalNames) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(x, y, untyped z);\n"
      "    @(posedge clk) x ##1 y ##1 z;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ModuleItem* seq = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) seq = item;
  }
  ASSERT_NE(seq, nullptr);
  ASSERT_EQ(seq->prop_formals.size(), 3u);
  EXPECT_EQ(seq->prop_formals[0], "x");
  EXPECT_EQ(seq->prop_formals[1], "y");
  EXPECT_EQ(seq->prop_formals[2], "z");
}

TEST(SequenceDeclarationParsing, SequenceDeclWithDefaultActualParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(x, y = 1'b1);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceDeclarationParsing, SequenceDeclWithTrailingLabelParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence : s\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceTypedFormalParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(sequence x);\n"
      "    @(posedge clk) x;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ModuleItem* seq = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      seq = item;
    }
  }
  ASSERT_NE(seq, nullptr);
  ASSERT_EQ(seq->prop_formals.size(), 1u);
  EXPECT_EQ(seq->prop_formals[0], "x");
}

TEST(SequenceDeclarationParsing, SequenceDeclEndLabelMismatchIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence : wrong\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "end label 'wrong' does not match 's'", 4,
                            "9.3.4"));
}

TEST(SequenceDeclarationParsing, DollarAsSequenceActualParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence delay_to(max);\n"
      "    @(posedge clk) a ##[1:max] b;\n"
      "  endsequence\n"
      "  sequence d_to_inf;\n"
      "    @(posedge clk) delay_to($);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceDeclarationParsing, NamedArgumentBindingParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence base(x, y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  sequence caller;\n"
      "    @(posedge clk) base(.x(a), .y(b));\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceDeclarationParsing, TypedFormalArgumentsParse) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(bit x, y, int z);\n"
      "    @(posedge clk) x ##1 y ##1 z;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInPackageParses) {
  auto r = Parse(
      "package p;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInInterfaceParses) {
  auto r = Parse(
      "interface ifc;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceBodyLocalVariableDeclIsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int cnt;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ModuleItem* seq = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      seq = item;
    }
  }
  ASSERT_NE(seq, nullptr);
  bool found_cnt = false;
  for (auto v : seq->prop_seq_assert_vars) {
    if (v == "cnt") found_cnt = true;
  }
  EXPECT_TRUE(found_cnt);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInProgramParses) {
  auto r = Parse(
      "program p;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInCompilationUnitScopeParses) {
  auto r = Parse(
      "sequence s;\n"
      "  @(posedge clk) a ##1 b;\n"
      "endsequence\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInCheckerParses) {
  auto r = Parse(
      "checker chk;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclaredInGenerateBlockParses) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    sequence s;\n"
      "      @(posedge clk) a ##1 b;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  bool found = false;
  for (auto* item : gen->gen_body) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(SequenceDeclarationParsing, SequenceDeclCapturesInstanceRefs) {
  auto r = Parse(
      "module m;\n"
      "  sequence inner;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence outer;\n"
      "    @(posedge clk) inner(c) ##1 d;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* outer = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "outer") {
      outer = item;
    }
  }
  ASSERT_NE(outer, nullptr);
  bool refs_inner = false;
  for (auto ref : outer->prop_instance_refs) {
    if (ref == "inner") refs_inner = true;
  }
  EXPECT_TRUE(refs_inner);
}

TEST(SequenceDeclaration, MalformedSequenceHeaderNames16_8) {
  auto r = Parse(
      "module m;\n"
      "  sequence s\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 3, "16.8"));
}

TEST(SequenceDeclaration, AFormalsDefaultActualIsRecorded) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  sequence s(x, y = b, shortint d = 3, untyped e = $inferred_clock,\n"
      "             sequence z = a ##1 b);\n"
      "    x ##d y;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_defaults.size(), 5u);
  EXPECT_EQ(item->prop_formal_defaults[0], nullptr);
  ASSERT_NE(item->prop_formal_defaults[1], nullptr);
  EXPECT_EQ(item->prop_formal_defaults[1]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->prop_formal_defaults[1]->text, "b");
  ASSERT_NE(item->prop_formal_defaults[2], nullptr);
  EXPECT_EQ(item->prop_formal_defaults[2]->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->prop_formal_defaults[3], nullptr);
  ASSERT_NE(item->prop_formal_defaults[4], nullptr);
  EXPECT_NE(item->prop_formal_defaults[4]->property_actual, nullptr);
}

TEST(SequenceDeclaration, AGuardedEventDefaultIsRecorded) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, en, a;\n"
      "  sequence s(event e = posedge clk iff en, untyped x = a);\n"
      "    @(e) x;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "e");
  EXPECT_EQ(item->prop_formals[1], "x");
  ASSERT_EQ(item->prop_formal_defaults.size(), 2u);
  const Expr* guarded = item->prop_formal_defaults[0];
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(guarded->kind, ExprKind::kBinary);
  EXPECT_EQ(guarded->op, TokenKind::kKwIff);
  ASSERT_NE(guarded->lhs, nullptr);
  EXPECT_EQ(guarded->lhs->op, TokenKind::kKwPosedge);
  ASSERT_NE(guarded->lhs->lhs, nullptr);
  EXPECT_EQ(guarded->lhs->lhs->text, "clk");
  ASSERT_NE(guarded->rhs, nullptr);
  EXPECT_EQ(guarded->rhs->text, "en");
  ASSERT_NE(item->prop_formal_defaults[1], nullptr);
  EXPECT_EQ(item->prop_formal_defaults[1]->text, "a");
}

TEST(SequenceDeclaration, AnOrEventDefaultIsRecorded) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, rst, a;\n"
      "  sequence s(untyped x, event e = posedge clk or rst);\n"
      "    @(e) x;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_defaults.size(), 2u);
  const Expr* either = item->prop_formal_defaults[1];
  ASSERT_NE(either, nullptr);
  EXPECT_EQ(either->kind, ExprKind::kBinary);
  EXPECT_EQ(either->op, TokenKind::kKwOr);
  ASSERT_NE(either->lhs, nullptr);
  EXPECT_EQ(either->lhs->op, TokenKind::kKwPosedge);
  ASSERT_NE(either->rhs, nullptr);
  EXPECT_EQ(either->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(either->rhs->text, "rst");
}

TEST(SequenceDeclaration, AnEventDefaultStoppingShortIsReported) {
  for (const char* dflt :
       {"posedge", "negedge", "posedge clk or", "edge clk or"}) {
    auto r = Parse(
        "module m;\n"
        "  logic clk, a;\n"
        "  sequence s(untyped x, event e = " +
        std::string(dflt) +
        ");\n"
        "    @(e) x;\n"
        "  endsequence\n"
        "endmodule\n");
    ASSERT_NE(r.cu, nullptr);
    EXPECT_TRUE(ReportedError(r.diags,
                              "a default actual argument opening with an edge "
                              "keyword is not an event expression",
                              3, "9.4.2"))
        << dflt;
    auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
    ASSERT_NE(item, nullptr);
    ASSERT_EQ(item->prop_formal_defaults.size(), 2u) << dflt;
    EXPECT_EQ(item->prop_formal_defaults[1], nullptr) << dflt;
  }
}

TEST(SequenceDeclaration, AChandleFormalIsReported) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(int n, chandle h); @(posedge clk) 1; endsequence\n"
      "  property p(chandle h, int n); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  constexpr char kMessage[] =
      "a sequence or property formal argument may not be of type chandle";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "16.8"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "16.8"));
}

TEST(SequenceDeclaration, AFormalOfAScopedTypeIsNamedAfterItself) {
  auto r = Parse(
      "package pk; typedef logic [1:0] t; endpackage\n"
      "class C #(int W = 1); typedef logic [W-1:0] t; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  sequence s(pk::t x, C#(8)::t y, z); @(posedge clk) 1; endsequence\n"
      "  property p(pk::t x, C#(8)::t y, z); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItemKind kKinds[] = {ModuleItemKind::kSequenceDecl,
                                   ModuleItemKind::kPropertyDecl};
  for (ModuleItemKind kind : kKinds) {
    auto* item = FindItemByKind(r, kind);
    ASSERT_NE(item, nullptr);
    ASSERT_EQ(item->prop_formals.size(), 3u);
    EXPECT_EQ(item->prop_formals[0], "x");
    EXPECT_EQ(item->prop_formals[1], "y");
    EXPECT_EQ(item->prop_formals[2], "z");
    ASSERT_EQ(item->prop_formal_types.size(), 3u);
    ASSERT_NE(item->prop_formal_types[0], nullptr);
    EXPECT_EQ(item->prop_formal_types[0]->scope_name, "pk");
    EXPECT_EQ(item->prop_formal_types[0]->type_name, "t");
    ASSERT_NE(item->prop_formal_types[1], nullptr);
    EXPECT_EQ(item->prop_formal_types[1]->scope_name, "C");
    EXPECT_EQ(item->prop_formal_types[1]->type_name, "t");
    EXPECT_EQ(item->prop_formal_types[2], item->prop_formal_types[1]);
  }
}

TEST(SequenceDeclaration, AFormalOfANamedTypeWithPackedDimsIsNamedAfterItself) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [1:0] my_t;\n"
      "  logic clk;\n"
      "  sequence s(my_t [3:0] x, y [2]); @(posedge clk) 1; endsequence\n"
      "  property p(my_t [3:0] x, y [2]); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItemKind kKinds[] = {ModuleItemKind::kSequenceDecl,
                                   ModuleItemKind::kPropertyDecl};
  for (ModuleItemKind kind : kKinds) {
    auto* item = FindItemByKind(r, kind);
    ASSERT_NE(item, nullptr);
    ASSERT_EQ(item->prop_formals.size(), 2u);
    EXPECT_EQ(item->prop_formals[0], "x");
    EXPECT_EQ(item->prop_formals[1], "y");
    ASSERT_EQ(item->prop_formal_types.size(), 2u);
    ASSERT_NE(item->prop_formal_types[0], nullptr);
    EXPECT_EQ(item->prop_formal_types[0]->type_name, "my_t");
    EXPECT_NE(item->prop_formal_types[0]->packed_dim_left, nullptr);
    EXPECT_EQ(item->prop_formal_types[1], item->prop_formal_types[0]);
  }
}

TEST(SequenceDeclaration, APortListEndingInsideAFormalsTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(my_t [3");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 2, "16.8"));
}

ModuleItem* FindSequenceIn(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSequenceDecl && item->name == "s") {
      return item;
    }
    for (const auto* nested : {&item->gen_body, &item->clocking_decls}) {
      if (auto* found = FindSequenceIn(*nested)) return found;
    }
  }
  return nullptr;
}

ModuleItem* FindSequenceS(const ParseResult& r) {
  for (const auto* units :
       {&r.cu->modules, &r.cu->interfaces, &r.cu->programs, &r.cu->checkers}) {
    for (auto* unit : *units) {
      if (auto* found = FindSequenceIn(unit->items)) return found;
    }
  }
  for (auto* pkg : r.cu->packages) {
    if (auto* found = FindSequenceIn(pkg->items)) return found;
  }
  return FindSequenceIn(r.cu->cu_items);
}

const char* const kEmptyListPlaces[] = {
    "module m;\n  sequence s(); a ##1 b; endsequence\nendmodule\n",
    "interface ifc;\n  sequence s(); a ##1 b; endsequence\nendinterface\n",
    "program pg;\n  sequence s(); a ##1 b; endsequence\nendprogram\n",
    ("module m;\n  clocking cb @(posedge clk);\n    sequence s(); a ##1 b; "
     "endsequence\n  endclocking\nendmodule\n"),
    "package pk;\n  sequence s(); a ##1 b; endsequence\nendpackage\n",
    "sequence s(); a ##1 b; endsequence\n",
    "checker ck;\n  sequence s(); a ##1 b; endsequence\nendchecker\n",
    ("module m;\n  if (1) begin : g\n    sequence s(); a ##1 b; endsequence\n"
     "  end\nendmodule\n"),
    ("module m;\n  for (genvar i = 0; i < 2; i++) begin : g\n    sequence s(); "
     "a ##1 b; endsequence\n  end\nendmodule\n")};

TEST(SequenceDeclarationParsing, EmptyParenthesesDeclareNoFormalsAnywhere) {
  for (const char* src : kEmptyListPlaces) {
    SCOPED_TRACE(src);
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    auto* seq = FindSequenceS(r);
    ASSERT_NE(seq, nullptr);
    EXPECT_TRUE(seq->prop_formals.empty());
  }
}

TEST(SequenceDeclarationParsing, NoParenthesesDeclareNoFormals) {
  auto r = Parse("module m;\n  sequence s; a ##1 b; endsequence\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* seq = FindSequenceS(r);
  ASSERT_NE(seq, nullptr);
  EXPECT_TRUE(seq->prop_formals.empty());
}

TEST(SequenceDeclarationParsing, ALoneCommaInThePortListIsReported) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(,);\n"
      "    a;\n"
      "  endsequence\n"
      "  sequence t();\n"
      "    a;\n"
      "  endsequence\n"
      "endmodule\n");
  const char* const kNoFormal =
      "sequence port item names a formal_port_identifier";
  EXPECT_TRUE(ReportedError(r.diags, kNoFormal, 2, "A.2.10"));
  EXPECT_FALSE(ReportedError(r.diags, kNoFormal, 5, "A.2.10"));
}

}  // namespace
