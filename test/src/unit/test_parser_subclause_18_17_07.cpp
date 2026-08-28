#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §18.17.7 governs value passing between randsequence productions: a production
// may carry a data_type_or_void return type and a tf_port_list of formal
// arguments. The grammar that admits these (rs_production) is owned by the
// parent §18.17; what §18.17.7 requires here is that the return type and the
// formal arguments be captured so the value-passing engine can act on them.
// These parser tests observe that capture.

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

// Parses a randsequence whose production `v` declares `type_text` as its
// return type, from a module carrying `decls` ahead of the initial block.
// §18.17's Syntax 18-13 writes the optional data_type_or_void immediately
// before the production identifier, so the cases below vary that text alone
// and share the module, the statement and the rule around it.
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

// The production named `v` in a run that accepted its source and recorded a
// return type on it, or nullptr when the run reported something or recorded no
// such production. Each case below then reads the one member of DataType that
// says which data_type form of A.2.2.1 was parsed.
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

// §18.17.7: a production with no data_type_or_void and no tf_port_list assumes
// a void return type and accepts no data — the parser records neither a return
// type nor any formal arguments.
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

// §18.17.7: an explicit 'void' return type is captured as such, distinguishing
// it from a value-returning production.
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

// §18.17.7: a non-void return type, including its packed dimensions, is parsed
// and retained so the production's return value can be sized correctly.
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
  // The [7:0] packed dimension is retained on the return type.
  EXPECT_NE(val->return_type.packed_dim_left, nullptr);
  EXPECT_NE(val->return_type.packed_dim_right, nullptr);
}

// §18.17.7: a production that accepts data declares a tf_port_list. The formal
// arguments — their names and declared types — are parsed and retained rather
// than discarded.
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

// §18.17.7: a formal argument may declare a default value (gen's "done"-style
// example). The default expression is retained on the formal.
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

// §18.17.7: a production may carry both a non-void return type and a
// tf_port_list at once (returning data requires a declared type; accepting data
// requires formal arguments). Both are parsed and retained on the same
// production.
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

// §18.17.7: a call site may pass more than one actual argument. Each is
// captured in the production item's argument list, in order.
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

// §18.17.7: defaults follow the task-prototype shape, so they are recorded per
// formal rather than all-or-nothing. With only the trailing formal defaulted,
// the parser retains a default on that formal alone and leaves the earlier one
// without one.
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

// §18.17.7: the return type a production declares is a data_type_or_void, and
// A.2.2.1 gives `data_type` a `[ class_scope | package_scope ] type_identifier
// { packed_dimension }` alternative — a name A.2.1.3's typedef declared. No
// keyword marks the type here, so the return type is recognized only from the
// parser's record of which identifiers name types; the production's own
// identifier is the one after it.
TEST(RandseqValuePassingParse, TypedefNameReturnTypeCaptured) {
  auto r = ParseProductionReturnType("  typedef int word;\n", "word");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(v->return_type.type_name, "word");
}

// §18.17.7 with A.2.2.1: `data_type ::= ... | enum [ enum_base_type ] {
// enum_name_declaration { , enum_name_declaration } } { packed_dimension }`,
// so an enumeration written out in place is a return type Syntax 18-13 admits.
// Its members are what an enum return type carries beyond the keyword, so they
// are read back rather than the kind alone.
TEST(RandseqValuePassingParse, EnumReturnTypeCaptured) {
  auto r = ParseProductionReturnType("", "enum { RED, GREEN }");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(v->return_type.enum_members.size(), 2u);
}

// §18.17.7 with A.2.2.1: `data_type ::= ... | struct_union [ packed [ signing ]
// ] { struct_union_member { struct_union_member } } { packed_dimension }`, so a
// structure written out in place is a return type Syntax 18-13 admits. Both
// members and the packed qualifier are read back, because they are what the
// return type has to carry for the value to be sized at all.
TEST(RandseqValuePassingParse, StructReturnTypeCaptured) {
  auto r = ParseProductionReturnType(
      "", "struct packed { bit [3:0] lo; bit [3:0] hi; }");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(v->return_type.is_packed);
  EXPECT_EQ(v->return_type.struct_members.size(), 2u);
}

// §18.17.7 with A.2.2.1: `data_type ::= integer_vector_type [ signing ] {
// packed_dimension }` and `integer_vector_type ::= bit | logic | reg`, so
// `reg signed [7:0]` is a signed vector return type Syntax 18-13 admits. It is
// written on `reg` because A.2.2.1 attaches the signing to a vector keyword: a
// bare `signed [7:0]` is an implicit_data_type, which data_type_or_void does
// not reach.
TEST(RandseqValuePassingParse, RegSignedVectorReturnTypeCaptured) {
  auto r = ParseProductionReturnType("", "reg signed [7:0]");
  const auto* v = ProductionWithReturnType(r);
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->return_type.kind, DataTypeKind::kReg);
  EXPECT_TRUE(v->return_type.is_signed);
  EXPECT_NE(v->return_type.packed_dim_left, nullptr);
}

}  // namespace
