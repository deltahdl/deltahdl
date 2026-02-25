// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// A.6.12 Randsequence — Elaboration
// =============================================================================
// Basic randsequence elaborates without errors
TEST(ElabA612, BasicRandsequenceElaborates) {
  ElabA612Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { ; };\n"
      "      second : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA70503Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA70503Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.7.5.3 Elab — edge_control_specifier
// =============================================================================
// edge_control_specifier with 01, 10 descriptors elaborates
TEST(ElabA70503, EdgeControlSpecifier01_10Elaborates) {
  ElabA70503Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [01, 10] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA81Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA81Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.8.1 Concatenations — Elaboration
// =============================================================================
// § concatenation elaborates in continuous assignment
TEST(ElabA81, ConcatenationInContAssign) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  assign a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_concatenation in parameter initialization
TEST(ElabA81, ConstantConcatenationInParam) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [15:0] P = {8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § multiple_concatenation (replication) in continuous assignment
TEST(ElabA81, ReplicationInContAssign) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  assign a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § streaming_concatenation elaborates in procedural context
TEST(ElabA81, StreamingConcatLeftShiftElab) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA81, StreamingConcatRightShiftElab) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § streaming_concatenation with slice_size elaborates
TEST(ElabA81, StreamingWithSliceSizeElab) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< byte {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § concatenation in initial block elaborates
TEST(ElabA81, ConcatInInitialBlock) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  initial a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § replication in initial block elaborates
TEST(ElabA81, ReplicateInInitialBlock) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  initial a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA82Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA82Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// § subroutine_call — nested function calls elaborate
TEST(ElabA82, NestedCallsElaborate) {
  ElabA82Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int n); return n + 1; endfunction\n"
      "  function int g(int n); return n * 2; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(g(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA83Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA83Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// § inside_expression — inside in initial block elaborates
TEST(ElabA83, InsideExprElaborates) {
  ElabA83Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic result;\n"
      "  initial result = x inside {8'd1, 8'd2, 8'd3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA84Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA84Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// § primary — hierarchical identifier with select elaborates
TEST(ElabA84, PrimaryHierIdentSelectElaborates) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — concatenation elaborates
TEST(ElabA84, PrimaryConcatenationElaborates) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] c;\n"
      "  initial c = {a, b};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA87Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA87Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// § unsigned_number — underscored decimal elaborates
TEST(ElabA87, UnderscoredDecimalElaborates) {
  ElabA87Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabCh511, ArrayInitPattern_NestedOk) {
  // §5.11: Nested braces matching array dimensions are valid.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabCh511, ArrayInitPattern_SizeMismatch) {
  // §10.9.1: Expressions shall match element for element; 3 != 2.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// =============================================================================
// Test fixture: sets up SimContext with an enum type and variable
// =============================================================================
struct EnumFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // Register an enum type with the given members and values.
  // Returns the variable associated with the enum.
  Variable* RegisterEnum(
      std::string_view var_name, std::string_view type_name,
      const std::vector<std::pair<std::string, uint64_t>>& members) {
    EnumTypeInfo info;
    char* tn = arena.AllocString(type_name.data(), type_name.size());
    info.type_name = std::string_view(tn, type_name.size());
    for (auto& [name, val] : members) {
      EnumMemberInfo m;
      char* mn = arena.AllocString(name.c_str(), name.size());
      m.name = std::string_view(mn, name.size());
      m.value = val;
      info.members.push_back(m);
    }
    ctx.RegisterEnumType(info.type_name, info);

    auto* var = ctx.CreateVariable(var_name, 32);
    var->value = MakeLogic4VecVal(arena, 32, members[0].second);
    ctx.SetVariableEnumType(var_name, info.type_name);
    return var;
  }

  // Build a method call expression: var_name.method_name(args...)
  Expr* MakeEnumMethodCall(std::string_view var_name,
                           std::string_view method_name) {
    return MakeEnumMethodCallWithArgs(var_name, method_name, {});
  }

  Expr* MakeEnumMethodCallWithArgs(std::string_view var_name,
                                   std::string_view method_name,
                                   std::vector<Expr*> args) {
    // Build: var_name.method_name(args...)
    auto* id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = var_name;

    auto* member = arena.Create<Expr>();
    member->kind = ExprKind::kIdentifier;
    member->text = method_name;

    auto* access = arena.Create<Expr>();
    access->kind = ExprKind::kMemberAccess;
    access->lhs = id;
    access->rhs = member;

    auto* call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->lhs = access;
    call->args = std::move(args);
    return call;
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }
};

TEST(EnumMethods, NameForUnknownValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);  // Not a valid member
  auto* call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // name() returns empty string for invalid enum values.
  EXPECT_EQ(result.ToUint64(), 0u);
}

struct EvalFixture {
  SourceManager mgr;
  Arena arena;
};

static Expr* ParseExprFrom(const std::string& src, EvalFixture& f) {
  std::string code = "module t #(parameter P = " + src + ") (); endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  DiagEngine diag(f.mgr);
  Lexer lexer(f.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, f.arena, diag);
  auto* cu = parser.Parse();
  EXPECT_FALSE(cu->modules.empty());
  EXPECT_FALSE(cu->modules[0]->params.empty());
  return cu->modules[0]->params[0].second;
}

TEST(ConstEval, ScopedIdentifier) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH", f), scope), 16);
}

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

TEST(StructType, FieldTypeKindPreserved) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "typed_s";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});
  f.ctx.RegisterStructType("typed_s", info);
  auto* found = f.ctx.FindStructType("typed_s");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->fields[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(found->fields[1].type_kind, DataTypeKind::kByte);
}

TEST(Elaboration, HardPackedUnion_DifferentWidth_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §10.9: assignment pattern with default key elaborates
TEST(ElabA60701, PatternDefaultKeyElaborates) {
  ElabA60701Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// --- §10.9.2: Struct assignment pattern validation ---
TEST(Elaboration, StructPattern_InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, StructPattern_DuplicateKey) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructPattern, NamedMemberTwoFields) {
  // '{x: 5, y: 10} on struct { logic [7:0] x; logic [7:0] y; }
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"x", "y"};
  pat->elements = {MakeIntLit(f.arena, 5), MakeIntLit(f.arena, 10)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberReversedOrder) {
  // '{y: 10, x: 5} — order-independent, same result
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"y", "x"};
  pat->elements = {MakeIntLit(f.arena, 10), MakeIntLit(f.arena, 5)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberThreeFields) {
  // '{r: 0xFF, g: 0x80, b: 0x00} on 24-bit struct
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "rgb_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8, DataTypeKind::kLogic});
  info.fields.push_back({"g", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"r", "g", "b"};
  pat->elements = {MakeIntLit(f.arena, 0xFF), MakeIntLit(f.arena, 0x80),
                   MakeIntLit(f.arena, 0x00)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFF8000u);
}

// =============================================================================
// §10.9.2 Structure assignment patterns — default and type-keyed
// =============================================================================
TEST(StructPattern, DefaultAllFields) {
  // '{default: 0xFF} → all fields filled with 0xFF
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"default"};
  pat->elements = {MakeIntLit(f.arena, 0xFF)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFFFu);
}

static Expr* ParseExprFrom(const std::string& src, AggFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

TEST(StructPattern, DefaultWithNamedOverride) {
  // '{a: 1, default: 0} → a=1, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 0)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0100u);
}

TEST(StructPattern, TypeKeyedInt) {
  // '{int: 42} on struct { int a; logic [7:0] b; } → a=42, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "mixed_t";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"int"};
  pat->elements = {MakeIntLit(f.arena, 42)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), uint64_t{42} << 8);
}

// =============================================================================
// §10.9 Assignment pattern evaluation
// =============================================================================
TEST(AssignmentPattern, PositionalTwoElements) {
  // '{a, b} with 8-bit variables → 16-bit packed result
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 8);
  auto* b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {a=5, b=10} → MSB-first: 5 in [15:8], 10 in [7:0] = 16'h050A
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPattern, SingleElement) {
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto* expr = ParseExprFrom("'{a}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(AssignmentPattern, EmptyPattern) {
  AggFixture f;
  auto* expr = ParseExprFrom("'{}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 0u);
}

TEST(AssignmentPattern, SizedLiterals) {
  // Test the parser fix for integer literal first elements
  AggFixture f;
  auto* expr = ParseExprFrom("'{32'd5, 32'd10}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Both are 32-bit (evaluator returns 32-bit for all int literals)
  // {32'd5, 32'd10} → 64-bit: upper=5, lower=10
  EXPECT_EQ(result.width, 64u);
  uint64_t expected = (uint64_t{5} << 32) | 10;
  EXPECT_EQ(result.ToUint64(), expected);
}

// § empty_unpacked_array_concatenation elaborates
TEST(ElabA81, EmptyUnpackedArrayConcatElab) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, ScopedExprWithParam) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8", f), scope), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH + 4", f), scope), 20);
}

TEST(ConstEval, Concatenation) {
  EvalFixture f;
  // {4'd3, 4'd5} = 8'h35 = 53
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4'd3, 4'd5}", f)), 0x35);
}

TEST(ConstEval, Replication) {
  EvalFixture f;
  // {4{1'b1}} = 4'b1111 = 15
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

// § constant_multiple_concatenation in parameter
TEST(ElabA81, ConstantMultipleConcatInParam) {
  ElabA81Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [31:0] P = {4{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — streaming concatenation elaborates
TEST(ElabA84, PrimaryStreamingConcatElaborates) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {<< 8 {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, WidthInference_Concatenation) {
  TypedefMap typedefs;
  Expr a;
  a.kind = ExprKind::kIntegerLiteral;
  a.int_val = 1;
  Expr b;
  b.kind = ExprKind::kIntegerLiteral;
  b.int_val = 2;
  Expr concat;
  concat.kind = ExprKind::kConcatenation;
  concat.elements = {&a, &b};
  EXPECT_EQ(InferExprWidth(&concat, typedefs), 64);  // 32 + 32
}

struct ElabA701Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA701Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.7.1 Specify block declaration — Elaboration
// =============================================================================
// Empty specify block elaborates without errors
TEST(ElabA701, EmptySpecifyBlockElaborates) {
  ElabA701Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with edge keyword elaborates
TEST(ElabA70503, TimingCheckEventEdgeKeywordElaborates) {
  ElabA70503Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

// --- §5: Source locations ---
TEST(LexerCh5, SourceLocations) {
  auto tokens = Lex("a\nb c");
  struct Case {
    size_t idx;
    int line;
    int column;
  };
  Case expected[] = {
      {0, 1, 1},
      {1, 2, 1},
      {2, 2, 3},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].loc.line, c.line) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].loc.column, c.column) << "token " << c.idx;
  }
}

TEST(LexerCh50603, DollarAloneIsNotSystemIdentifier) {
  // §5.6.3: Grammar requires >= 1 char after $; bare $ is kDollar.
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  // 10 delay units at 1ns with 1ps precision = 10,000 ticks.
  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

// Sim test fixture
struct SimA604Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimA604Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// =============================================================================
// A.6.4 Statements — Simulation
// =============================================================================
// ---------------------------------------------------------------------------
// Simulation: statement_or_null and statement execution
// ---------------------------------------------------------------------------
// §12.3: null statement has no effect in simulation
TEST(SimA604, NullStatementNoEffect) {
  SimA604Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    ;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
