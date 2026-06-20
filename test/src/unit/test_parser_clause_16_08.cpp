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
