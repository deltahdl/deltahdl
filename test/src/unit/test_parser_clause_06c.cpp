#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult6c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult6c Parse(const std::string &src) {
  ParseResult6c result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 6.10 -- Implicit declarations
// =============================================================================

TEST(ParserSection6, ImplicitNetInPortList) {
  auto r = Parse("module m(a, b);\n"
                 "  input a;\n"
                 "  output b;\n"
                 "  assign b = a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ParserSection6, ImplicitNetInContAssign) {
  auto r = Parse("module m;\n"
                 "  assign out = in1 & in2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, ImplicitNetInModuleInst) {
  auto r = Parse("module m;\n"
                 "  sub u1(.a(w1), .b(w2));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, DefaultNettypeAffectsImplicit) {
  auto r = Parse("`default_nettype none\n"
                 "module m;\n"
                 "  wire w;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 6.18 -- User-defined types (typedef)
// =============================================================================

TEST(ParserSection6, TypedefStruct) {
  auto r = Parse("module m;\n"
                 "  typedef struct { int x; int y; } point_t;\n"
                 "  point_t p;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto *td = r.cu->modules[0]->items[0];
  EXPECT_EQ(td->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(td->name, "point_t");
}

TEST(ParserSection6, TypedefEnum) {
  auto r = Parse("module m;\n"
                 "  typedef enum { IDLE, RUN, DONE } state_t;\n"
                 "  state_t s;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *td = r.cu->modules[0]->items[0];
  EXPECT_EQ(td->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(td->typedef_type.kind, DataTypeKind::kEnum);
}

TEST(ParserSection6, TypedefForwardClass) {
  auto r = Parse("typedef class MyClass;\n"
                 "class MyClass;\n"
                 "  int x;\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, TypedefForwardStruct) {
  auto r = Parse("module m;\n"
                 "  typedef struct my_struct;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypedefUnion) {
  auto r = Parse("module m;\n"
                 "  typedef union { int i; real r; } num_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 6.20 -- Type operator
// =============================================================================

TEST(ParserSection6, TypeExprInCast) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = int'(3.14);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypeRefInBitsCast) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $bits(int);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, TypeOperatorTypeOf) {
  auto r = Parse("module m;\n"
                 "  int a;\n"
                 "  initial begin\n"
                 "    $display(\"%0d\", $typename(a));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 6.22.2 -- Compatible types
// =============================================================================

TEST(ParserSection6, CompatibleTypesParseLogicVectors) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  logic [7:0] b;\n"
                 "  assign a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, CompatibleTypesIntToLogic) {
  auto r = Parse("module m;\n"
                 "  int a;\n"
                 "  logic [31:0] b;\n"
                 "  initial a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, CompatibleTypesNamedType) {
  auto r = Parse("module m;\n"
                 "  typedef logic [7:0] byte_t;\n"
                 "  byte_t a;\n"
                 "  byte_t b;\n"
                 "  assign a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 6.22.3 -- Assignment compatible types
// =============================================================================

TEST(ParserSection6, AssignCompatibleIntToReal) {
  auto r = Parse("module m;\n"
                 "  real r;\n"
                 "  initial r = 42;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, AssignCompatibleRealToInt) {
  auto r = Parse("module m;\n"
                 "  int x;\n"
                 "  initial x = 3.14;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, AssignCompatibleStringLiteral) {
  auto r = Parse("module m;\n"
                 "  string s;\n"
                 "  initial s = \"hello\";\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
