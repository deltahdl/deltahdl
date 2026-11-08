#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

const RsProduction* FindProd(const Stmt* stmt, std::string_view name) {
  for (const auto& p : stmt->rs_productions) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

const Stmt* RandseqStmt(ParseResult& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->kind == StmtKind::kRandsequence ? stmt : nullptr;
}

ParseResult ParseProductionReturnType(std::string_view decls,
                                      std::string_view type_text) {
  return Parse(std::string("module m;\n") + std::string(decls) +
               "  initial begin\n"
               "    randsequence(main)\n"
               "      void main : v ;\n"
               "      " +
               std::string(type_text) +
               " v : { return 7; } ;\n"
               "    endsequence\n"
               "  end\n"
               "endmodule\n");
}

const RsProduction* ProductionWithReturnType(ParseResult& r) {
  EXPECT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  if (stmt == nullptr) return nullptr;
  const auto* v = FindProd(stmt, "v");
  if (v == nullptr) return nullptr;
  EXPECT_TRUE(v->has_return_type);
  return v;
}

TEST(RandseqValuePassingParse, PlainProductionHasNoTypeNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a ;\n"
      "      a : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* a = FindProd(stmt, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_FALSE(a->has_return_type);
  EXPECT_FALSE(a->has_ports);
  EXPECT_TRUE(a->ports.empty());
}

TEST(RandseqValuePassingParse, VoidReturnTypeCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(top)\n"
      "      void top : a ;\n"
      "      a : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* top = FindProd(stmt, "top");
  ASSERT_NE(top, nullptr);
  EXPECT_TRUE(top->has_return_type);
  EXPECT_EQ(top->return_type.kind, DataTypeKind::kVoid);
}

TEST(RandseqValuePassingParse, VectorReturnTypeCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      void main : val ;\n"
      "      bit [7:0] val : { return 8'hAB; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* val = FindProd(stmt, "val");
  ASSERT_NE(val, nullptr);
  EXPECT_TRUE(val->has_return_type);
  EXPECT_EQ(val->return_type.kind, DataTypeKind::kBit);
  EXPECT_NE(val->return_type.packed_dim_left, nullptr);
  EXPECT_NE(val->return_type.packed_dim_right, nullptr);
}

TEST(RandseqValuePassingParse, FormalArgumentListCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen ;\n"
      "      gen : compute(5) ;\n"
      "      compute( int a, bit [3:0] b ) : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* compute = FindProd(stmt, "compute");
  ASSERT_NE(compute, nullptr);
  EXPECT_TRUE(compute->has_ports);
  ASSERT_EQ(compute->ports.size(), 2u);
  EXPECT_EQ(compute->ports[0].name, "a");
  EXPECT_EQ(compute->ports[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(compute->ports[1].name, "b");
  EXPECT_EQ(compute->ports[1].data_type.kind, DataTypeKind::kBit);
}

TEST(RandseqValuePassingParse, FormalArgumentDefaultCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen ;\n"
      "      gen( int s = 7 ) : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* gen = FindProd(stmt, "gen");
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->ports.size(), 1u);
  EXPECT_EQ(gen->ports[0].name, "s");
  EXPECT_NE(gen->ports[0].default_value, nullptr);
}

TEST(RandseqValuePassingParse, ReturnTypeAndPortsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      void main : gen ;\n"
      "      int gen( bit [3:0] a ) : { return a; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* gen = FindProd(stmt, "gen");
  ASSERT_NE(gen, nullptr);
  EXPECT_TRUE(gen->has_return_type);
  EXPECT_EQ(gen->return_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(gen->has_ports);
  ASSERT_EQ(gen->ports.size(), 1u);
  EXPECT_EQ(gen->ports[0].name, "a");
  EXPECT_EQ(gen->ports[0].data_type.kind, DataTypeKind::kBit);
}

TEST(RandseqValuePassingParse, MultipleCallSiteArgumentsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : combine(1, 2, 3) ;\n"
      "      combine( int a, int b, int c ) : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* main = FindProd(stmt, "main");
  ASSERT_NE(main, nullptr);
  ASSERT_EQ(main->rules.size(), 1u);
  ASSERT_EQ(main->rules[0].prods.size(), 1u);
  const auto& item = main->rules[0].prods[0];
  EXPECT_EQ(item.item.name, "combine");
  ASSERT_EQ(item.item.args.size(), 3u);
}

TEST(RandseqValuePassingParse, FormalArgumentDefaultAmongMultiple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : combine(3) ;\n"
      "      combine( int a, int b = 5 ) : { ; } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* stmt = RandseqStmt(r);
  ASSERT_NE(stmt, nullptr);
  const auto* combine = FindProd(stmt, "combine");
  ASSERT_NE(combine, nullptr);
  ASSERT_EQ(combine->ports.size(), 2u);
  EXPECT_EQ(combine->ports[0].name, "a");
  EXPECT_EQ(combine->ports[0].default_value, nullptr);
  EXPECT_EQ(combine->ports[1].name, "b");
  EXPECT_NE(combine->ports[1].default_value, nullptr);
}

TEST(RandseqValuePassingParse, TypedefNameReturnTypeCaptured) {
  auto r = ParseProductionReturnType("  typedef int word;\n", "word");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(v->return_type.type_name, "word");
}

TEST(RandseqValuePassingParse, VectorTypedefNameReturnTypeCaptured) {
  auto r = ParseProductionReturnType("  typedef bit [3:0] nib;\n", "nib");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(v->return_type.type_name, "nib");
}

TEST(RandseqValuePassingParse, EnumReturnTypeCaptured) {
  auto r = ParseProductionReturnType("", "enum { RED, GREEN }");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(v->return_type.enum_members.size(), 2u);
}

TEST(RandseqValuePassingParse, StructReturnTypeCaptured) {
  auto r = ParseProductionReturnType(
      "", "struct packed { bit [3:0] lo; bit [3:0] hi; }");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(v->return_type.is_packed);
  EXPECT_EQ(v->return_type.struct_members.size(), 2u);
}

TEST(RandseqValuePassingParse, RegSignedVectorReturnTypeCaptured) {
  auto r = ParseProductionReturnType("", "reg signed [7:0]");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kReg);
  EXPECT_TRUE(v->return_type.is_signed);
  EXPECT_NE(v->return_type.packed_dim_left, nullptr);
}

TEST(RandseqValuePassingParse, BareSigningReturnTypeIsRejected) {
  auto r = ParseProductionReturnType("", "signed [7:0]");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a randsequence production return type shall be a "
                            "data type or 'void'",
                            5, "18.17"));
}

TEST(RandseqValuePassingParse, BarePackedDimensionReturnTypeIsRejected) {
  auto r = ParseProductionReturnType("", "[7:0]");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a randsequence production return type shall be a "
                            "data type or 'void'",
                            5, "18.17"));
}

}  // namespace
