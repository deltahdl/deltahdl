#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static CompilationUnit* ParseSrc(const std::string& src, ParseFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

TEST(IdentifierSyntaxParsing, PsTypeIdentifierFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalTfIdentifierPackageScopedCall) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  function int helper(int x); return x + 1; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = pkg::helper(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, EscapedIdentifierInExpr) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic \\busy-signal ;\n"
      "  assign \\busy-signal = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsClassIdentifierFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  class my_class;\n"
      "    int x;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::my_class h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsParameterIdentifierFromGenerateBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "      localparam int LOCAL_P = 1;\n"
      "    end\n"
      "  endgenerate\n"
      "  logic [gen_blk[0].LOCAL_P-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalNetIdentifierAcrossPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [pkg::W-1:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ModportIdentifierAfterDot) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_if;\n"
      "  logic d;\n"
      "  modport mp(input d);\n"
      "endinterface\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, NettypeIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  nettype real my_real_net;\n"
      "endpackage\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SimpleIdentifierAllowsUnderscoreAndDigits) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m_1;\n"
      "  logic abc_2_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->modules[0]->name, "m_1");
}

TEST(IdentifierSyntaxParsing, HierarchicalIdentifierTfCall) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub;\n"
      "  function int helper(); return 1; endfunction\n"
      "endmodule\n"
      "module m;\n"
      "  sub u();\n"
      "  int y;\n"
      "  initial y = u.helper();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalPropertyIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub(input clk, input a);\n"
      "  property p_ok;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n"
      "module m(input clk, input a);\n"
      "  sub u(.clk(clk), .a(a));\n"
      "  assert property (u.p_ok);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalSequenceIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub(input clk, input a, input b);\n"
      "  sequence s_ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n"
      "module m(input clk, input a, input b);\n"
      "  sub u(.clk(clk), .a(a), .b(b));\n"
      "  cover property (u.s_ab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, IndexVariableIdentifierInForeach) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  int data [4];\n"
      "  initial begin\n"
      "    foreach (data[idx]) data[idx] = idx;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ConstraintIdentifierInClass) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  rand int x;\n"
      "  constraint c_range { x > 0; x < 10; }\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->classes.empty());
  bool found = false;
  for (auto* m : cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == "c_range") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IdentifierSyntaxParsing, ClockingIdentifierInClockingBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input clk, input d);\n"
      "  clocking cb @(posedge clk);\n"
      "    input d;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->modules.empty());
  bool found = false;
  for (auto* item : cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock && item->name == "cb") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IdentifierSyntaxParsing, UdpIdentifierInPrimitive) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "primitive my_buf (out, in);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->udps.size(), 1u);
  EXPECT_EQ(cu->udps[0]->name, "my_buf");
}

TEST(IdentifierSyntaxParsing, MethodIdentifierInClass) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  function int get_x();\n"
      "    return 7;\n"
      "  endfunction\n"
      "  task do_thing();\n"
      "  endtask\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->classes.empty());
  bool saw_func = false;
  bool saw_task = false;
  for (auto* m : cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      if (m->method->name == "get_x") saw_func = true;
      if (m->method->name == "do_thing") saw_task = true;
    }
  }
  EXPECT_TRUE(saw_func);
  EXPECT_TRUE(saw_task);
}

TEST(IdentifierSyntaxParsing, BlockIdentifierOnSequentialBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin : init_blk\n"
      "    logic x;\n"
      "    x = 1'b0;\n"
      "  end : init_blk\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsIdentifierGenericFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  int counter = 0;\n"
      "endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = pkg::counter;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, TerminalIdentifierInUdpPort) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "primitive p_inv (q, a);\n"
      "  output q;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->udps.size(), 1u);
  EXPECT_EQ(cu->udps[0]->output_name, "q");
  ASSERT_EQ(cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(cu->udps[0]->input_names[0], "a");
}

TEST(IdentifierSyntaxParsing, InterfacePortIdentifierAsModulePort) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_if;\n"
      "  logic d;\n"
      "endinterface\n"
      "module m(my_if iface);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The right-hand operand of the one relation the parsed class's one
// constraint block holds.
//
// A constraint block states its relations as expressions, so a test about the
// syntax admitted on one side of a relation parses a class carrying a single
// constraint and reads that side back. Returns nullptr when no constraint
// member, no single relation, or no binary relation was produced.
const Expr* SoleConstraintRelationRhs(const CompilationUnit* cu) {
  if (cu == nullptr || cu->classes.empty()) return nullptr;
  const ClassMember* con = nullptr;
  for (auto* m : cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) con = m;
  }
  if (con == nullptr || con->constraint_exprs.size() != 1u) return nullptr;
  const Expr* rel = con->constraint_exprs[0];
  if (rel->kind != ExprKind::kBinary) return nullptr;
  return rel->rhs;
}

// §A.9.3: ps_type_identifier admits a "local ::" scope prefix (footnote 48),
// which names a value in the enclosing scope of an inline randomize()...with
// constraint rather than the randomized object (see 18.7.1). The parser accepts
// "local::name" as a scope-resolution chain, so the constraint relation that
// references it is captured; without that acceptance the speculative relation
// parse bails on the 'local' keyword and drops the relation entirely.
TEST(IdentifierSyntaxParsing, LocalScopePrefixInConstraintRelation) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  rand int x;\n"
      "  constraint lim { x == local::y; }\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const Expr* rhs = SoleConstraintRelationRhs(cu);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kMemberAccess);
  EXPECT_TRUE(rhs->is_scope_resolution);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->text, "local");
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "y");
}

// §A.9.3: a ps_type_identifier is a simple_type, so the "local ::"-prefixed
// form may serve as the casting_type of a cast ("local::T'(expr)"). Verify the
// scoped type name is parsed as the cast's target type.
TEST(IdentifierSyntaxParsing, LocalScopePrefixCastType) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  rand int x;\n"
      "  constraint lim { x == local::word_t'(y); }\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const Expr* rhs = SoleConstraintRelationRhs(cu);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kCast);
  const Expr* casting_type = rhs->rhs;
  ASSERT_NE(casting_type, nullptr);
  ASSERT_EQ(casting_type->kind, ExprKind::kMemberAccess);
  EXPECT_TRUE(casting_type->is_scope_resolution);
  ASSERT_NE(casting_type->lhs, nullptr);
  EXPECT_EQ(casting_type->lhs->text, "local");
  ASSERT_NE(casting_type->rhs, nullptr);
  EXPECT_EQ(casting_type->rhs->text, "word_t");
}

// §A.9.3: ps_type_identifier's class_scope alternative — a type nested in a
// class is named by qualifying it with the class ("C::T"). This exercises the
// third prefix form of the production (the package_scope and local:: forms are
// covered by PsTypeIdentifierFromPackage and LocalScopePrefix* above).
TEST(IdentifierSyntaxParsing, PsTypeIdentifierFromClassScope) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class container;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "endclass\n"
      "module m;\n"
      "  container::nibble_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.9.3: class_variable_identifier ::= variable_identifier — a variable whose
// data type is a class handle is named by an ordinary identifier.
TEST(IdentifierSyntaxParsing, ClassVariableIdentifierDecl) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_class handle;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.9.3: ps_parameter_identifier's class_scope alternative — a parameter
// declared inside a class is referenced by qualifying it with the class
// ("C::P"). The package_scope form is covered by PsParameterFromPackageResolves
// and the generate_block form by PsParameterIdentifierFromGenerateBlock.
TEST(IdentifierSyntaxParsing, PsParameterIdentifierFromClassScope) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class cfg;\n"
      "  localparam int WIDTH = 16;\n"
      "endclass\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = cfg::WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.9.3: c_identifier ::= [ a-zA-Z_ ] { [ a-zA-Z0-9_ ] } — the first character
// may be an underscore as well as a letter. A DPI import linkage name that
// begins with '_' is accepted (the letter-first form is covered by
// DpiImportWithCIdentifier).
TEST(IdentifierSyntaxParsing, DpiImportCIdentifierLeadingUnderscore) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" _c_func = function void sv_func();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->dpi_c_name, "_c_func");
  EXPECT_EQ(item->name, "sv_func");
}

}  // namespace
