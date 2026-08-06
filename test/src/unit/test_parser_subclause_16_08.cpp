#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  // §16.8 sequence_port_list: each formal_port_identifier must be recoverable
  // from the parsed declaration so later stages can bind actuals and check
  // typed-vs-untyped rules.
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
  // §16.8: a default actual argument may be specified for a formal argument
  // in the optional associated declaration assignment.
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
  // §16.8 sequence_declaration: `endsequence [ : sequence_identifier ]`.
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
  // §16.8 Syntax 16-5, sequence_formal_type ::= data_type_or_implicit
  // | sequence | untyped. The `sequence` alternative (a formal that is itself
  // a sequence) must parse and its formal_port_identifier must be captured.
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
  // §16.8 sequence_declaration: `endsequence [ : sequence_identifier ]`. When
  // the trailing label is present it must match the declared sequence name;
  // a mismatched label is rejected. This is the negative of the accepting
  // SequenceDeclWithTrailingLabelParses case.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence : wrong\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceDeclarationParsing, DollarAsSequenceActualParses) {
  // §16.8: the terminal `$` may appear as an actual argument in a sequence
  // instance (here as the upper bound of a cycle_delay_const_range).
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
  // §16.8: actuals may be bound to formals by name using the
  // `.formal_port_identifier(actual)` form.
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
  // §16.8: a formal argument may be typed by specifying its type prior to
  // the formal_port_identifier; the type carries through to subsequent
  // identifiers until a new type appears.
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
  // §16.8 scope list: a named sequence may be declared in a package.
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
  // §16.8 scope list: a named sequence may be declared in an interface.
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
  // §16.8 Syntax 16-5: a sequence_declaration admits an optional run of
  // assertion_variable_declarations between the header and the sequence_expr
  // ({ assertion_variable_declaration } sequence_expr). The parser harvests
  // each declared local name so later stages can bind it; observe that a
  // body-local variable is recorded on the declaration.
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
  // §16.8 scope list: a named sequence may be declared in a program. The
  // program body reaches the sequence parser through ParseModuleItem, a
  // distinct container from a module or package.
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
  // §16.8 scope list: a named sequence may be declared in compilation-unit
  // scope, i.e. outside any design element. It lands in the unit's cu_items.
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
  // §16.8 scope list: a named sequence may be declared in a checker.
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
  // §16.8 scope list: a named sequence may be declared in a generate block.
  // Here the sequence lives inside a generate-for block's body, a scope
  // distinct from a bare module item.
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
  // §16.8 cyclic-dependency check needs to know which named sequences a
  // declaration instantiates inside its body.
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

}  // namespace
