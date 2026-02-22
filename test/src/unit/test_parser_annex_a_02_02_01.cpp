#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

} // namespace

// =============================================================================
// A.2.2.1 Net and variable types
// =============================================================================

// --- casting_type ---
// simple_type | constant_primary | signing | string | const

TEST(ParserA221, CastingTypeSimpleInt) {
  // simple_type: integer_type cast
  auto r = Parse("module m;\n"
                 "  initial begin int x; x = int'(3.14); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeSigning) {
  // signing: signed'(val)
  auto r = Parse("module m;\n"
                 "  initial begin int x; x = signed'(8'hFF); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeString) {
  // string: string'(val)
  auto r = Parse("module m;\n"
                 "  initial begin string s; s = string'(65); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeConst) {
  // const: const'(expr)
  auto r = Parse("module m;\n"
                 "  initial begin int x; x = const'(42); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeUserDefined) {
  // casting_type with user-defined type (simple_type: ps_type_identifier)
  // Note: constant_primary'(expr) cast (e.g., N'(val)) requires semantic
  // analysis to distinguish from sized literals — tested via type casts.
  auto r = Parse("module m;\n"
                 "  typedef logic [7:0] byte_t;\n"
                 "  initial begin byte_t x; x = byte_t'(16'hFF); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- data_type --- (12 alternatives)
// integer_vector_type [signing] {packed_dimension}

TEST(ParserA221, DataTypeIntegerVector) {
  auto r = Parse("module m; logic signed [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

// integer_atom_type [signing]

TEST(ParserA221, DataTypeIntegerAtom) {
  auto r = Parse("module m; int unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
}

// non_integer_type

TEST(ParserA221, DataTypeNonInteger) {
  auto r = Parse("module m; real x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kReal);
}

// struct_union [packed [signing]] { ... } {packed_dimension}

TEST(ParserA221, DataTypeStructPacked) {
  auto r =
      Parse("module m;\n"
            "  struct packed signed { logic [7:0] a; logic [7:0] b; } pair;\n"
            "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

// enum [enum_base_type] { ... } {packed_dimension}

TEST(ParserA221, DataTypeEnum) {
  auto r = Parse("module m; enum logic [1:0] {A, B, C} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

// string

TEST(ParserA221, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}

// chandle

TEST(ParserA221, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kChandle);
}

// virtual [interface] interface_identifier [parameter_value_assignment]
//   [. modport_identifier]

TEST(ParserA221, DataTypeVirtualInterface) {
  auto r = Parse("interface my_ifc; endinterface\n"
                 "module m; virtual interface my_ifc vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "my_ifc");
}

// [class_scope | package_scope] type_identifier {packed_dimension}

TEST(ParserA221, DataTypeScopedType) {
  auto r = Parse("package pkg;\n"
                 "  typedef int my_int_t;\n"
                 "endpackage\n"
                 "module m;\n"
                 "  import pkg::*;\n"
                 "  pkg::my_int_t x;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_type (ps_class_identifier [param] { :: class_identifier [param] })

TEST(ParserA221, DataTypeClassType) {
  auto r = Parse("class my_cls;\n"
                 "  typedef int my_type;\n"
                 "endclass\n"
                 "module m; my_cls::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// event

TEST(ParserA221, DataTypeEvent) {
  auto r = Parse("module m; event ev; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEvent);
}

// type_reference (type(expression) | type(data_type))

TEST(ParserA221, DataTypeTypeReference) {
  // A.2.2.1: data_type ::= ... | type_reference
  // type(expr) used as data_type in a declaration (without 'var' prefix)
  auto r = Parse("module m;\n"
                 "  int a;\n"
                 "  type(a) b;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto *item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(item->data_type.type_ref_expr, nullptr);
}

// --- data_type_or_implicit ---
// data_type | implicit_data_type

// --- implicit_data_type ---
// [signing] {packed_dimension}

TEST(ParserA221, ImplicitDataType) {
  // Implicit data type with just packed dimension
  auto r = Parse("module m(input [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, ImplicitDataTypeSigned) {
  // signed [7:0]
  auto r = Parse("module m(input signed [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_signed);
}

// --- enum_base_type ---
// integer_atom_type [signing] | integer_vector_type [signing] [packed_dim]
// | type_identifier [packed_dimension]

TEST(ParserA221, EnumBaseAtomType) {
  auto r = Parse("module m; enum int {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

TEST(ParserA221, EnumBaseVectorWithDim) {
  auto r = Parse("module m; enum logic [7:0] {A=0, B=255} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->items[0]->data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, EnumBaseTypeIdentifier) {
  // enum type_identifier { ... }
  auto r = Parse("module m;\n"
                 "  typedef logic [3:0] nibble_t;\n"
                 "  enum nibble_t {A, B} x;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- enum_name_declaration ---
// enum_id [ [ integral_number [ : integral_number ] ] ] [ = const_expr ]

TEST(ParserA221, EnumNameBasic) {
  auto r = Parse("module m; enum {RED, GREEN, BLUE} color; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.enum_members.size(), 3u);
}

TEST(ParserA221, EnumNameWithRange) {
  // enum_id [ integral_number ]
  auto r = Parse("module m; enum {A[3]} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
}

TEST(ParserA221, EnumNameWithRangeColon) {
  // enum_id [ integral_number : integral_number ]
  auto r = Parse("module m; enum {A[0:3] = 10} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

// --- class_scope ---
// class_type ::

TEST(ParserA221, ClassScope) {
  auto r = Parse("class base_cls;\n"
                 "  typedef int inner_t;\n"
                 "endclass\n"
                 "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- class_type ---
// ps_class_identifier [param] { :: class_identifier [param] }

TEST(ParserA221, ClassTypeParameterized) {
  auto r = Parse("class param_cls #(type T = int);\n"
                 "  typedef T value_t;\n"
                 "endclass\n"
                 "module m; param_cls#(int)::value_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- interface_class_type ---
// ps_class_identifier [parameter_value_assignment]
// (grammatically same as single class_type)

// --- integer_type ---
// integer_vector_type | integer_atom_type

// --- integer_atom_type ---
// byte | shortint | int | longint | integer | time

TEST(ParserA221, IntegerAtomTypes) {
  auto r = Parse("module m;\n"
                 "  byte a;\n"
                 "  shortint b;\n"
                 "  int c;\n"
                 "  longint d;\n"
                 "  integer e;\n"
                 "  time f;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind,
            DataTypeKind::kShortint);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(r.cu->modules[0]->items[3]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(r.cu->modules[0]->items[4]->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(r.cu->modules[0]->items[5]->data_type.kind, DataTypeKind::kTime);
}

// --- integer_vector_type ---
// bit | logic | reg

TEST(ParserA221, IntegerVectorTypes) {
  auto r = Parse("module m;\n"
                 "  bit a;\n"
                 "  logic b;\n"
                 "  reg c;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind, DataTypeKind::kReg);
}

// --- non_integer_type ---
// shortreal | real | realtime

TEST(ParserA221, NonIntegerTypes) {
  auto r = Parse("module m;\n"
                 "  shortreal a;\n"
                 "  real b;\n"
                 "  realtime c;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind,
            DataTypeKind::kShortreal);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind,
            DataTypeKind::kRealtime);
}

// --- net_type ---
// supply0|supply1|tri|triand|trior|trireg|tri0|tri1|uwire|wire|wand|wor

TEST(ParserA221, NetTypeVariants) {
  auto r = Parse("module m;\n"
                 "  supply0 s0;\n"
                 "  supply1 s1;\n"
                 "  tri t;\n"
                 "  triand ta;\n"
                 "  trior to2;\n"
                 "  trireg tr;\n"
                 "  tri0 t0;\n"
                 "  tri1 t1;\n"
                 "  uwire uw;\n"
                 "  wire w;\n"
                 "  wand wa;\n"
                 "  wor wo;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kTri);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kTriand);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kTrior);
  EXPECT_EQ(items[5]->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(items[6]->data_type.kind, DataTypeKind::kTri0);
  EXPECT_EQ(items[7]->data_type.kind, DataTypeKind::kTri1);
  EXPECT_EQ(items[8]->data_type.kind, DataTypeKind::kUwire);
  EXPECT_EQ(items[9]->data_type.kind, DataTypeKind::kWire);
  EXPECT_EQ(items[10]->data_type.kind, DataTypeKind::kWand);
  EXPECT_EQ(items[11]->data_type.kind, DataTypeKind::kWor);
}

// --- net_port_type ---
// [net_type] data_type_or_implicit | nettype_identifier
// | interconnect implicit_data_type

TEST(ParserA221, NetPortTypeWithNetType) {
  auto r = Parse("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ParserA221, NetPortTypeInterconnect) {
  // interconnect implicit_data_type
  // Note: interconnect in ANSI port list requires port-parser extensions;
  // tested here in module body per A.2.1.3 net_declaration form 3.
  auto r = Parse("module m; interconnect [7:0] net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_interconnect);
}

// --- variable_port_type ---
// var_data_type ::= data_type | var data_type_or_implicit

TEST(ParserA221, VarDataTypeExplicit) {
  auto r = Parse("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kInt);
}

TEST(ParserA221, VarDataTypeWithVar) {
  // var data_type_or_implicit
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- signing ---
// signed | unsigned

TEST(ParserA221, SigningSigned) {
  auto r = Parse("module m; logic signed [7:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

TEST(ParserA221, SigningUnsigned) {
  auto r = Parse("module m; integer unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

// --- simple_type ---
// integer_type | non_integer_type | ps_type_identifier |
// ps_parameter_identifier (covered by casting_type and data_type tests above)

// --- struct_union ---
// struct | union [soft | tagged]

TEST(ParserA221, StructUnionStruct) {
  auto r = Parse("module m;\n"
                 "  struct { int a; int b; } s;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kStruct);
}

TEST(ParserA221, StructUnionUnionTagged) {
  auto r = Parse("module m;\n"
                 "  union tagged { int a; real b; } u;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_tagged);
}

TEST(ParserA221, StructUnionUnionSoft) {
  auto r = Parse("module m;\n"
                 "  union soft { int a; real b; } u;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_soft);
}

// --- struct_union_member ---
// {attribute_instance} [random_qualifier] data_type_or_void
//   list_of_variable_decl_assignments ;

TEST(ParserA221, StructMemberBasic) {
  auto r = Parse("module m;\n"
                 "  struct { logic [7:0] data; int count; } s;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  EXPECT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0].name, "data");
  EXPECT_EQ(members[1].name, "count");
}

TEST(ParserA221, StructMemberRand) {
  // random_qualifier: rand
  auto r = Parse("module m;\n"
                 "  struct { rand int a; int b; } s;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0].is_rand);
  EXPECT_FALSE(members[1].is_rand);
}

TEST(ParserA221, StructMemberRandc) {
  // random_qualifier: randc
  auto r = Parse("module m;\n"
                 "  struct { randc bit [7:0] x; } s;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 1u);
  EXPECT_TRUE(members[0].is_randc);
}

TEST(ParserA221, StructMemberAttr) {
  // {attribute_instance} before struct member
  auto r = Parse("module m;\n"
                 "  struct { (* mark *) int a; int b; } s;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_FALSE(members[0].attrs.empty());
  EXPECT_TRUE(members[1].attrs.empty());
}

// --- data_type_or_void ---
// data_type | void

TEST(ParserA221, DataTypeOrVoidReturn) {
  // void as function return type (data_type_or_void)
  auto r = Parse("module m;\n"
                 "  function void do_nothing; endfunction\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// --- type_reference ---
// type ( expression ) | type ( data_type_or_incomplete_class_scoped_type )

TEST(ParserA221, TypeRefExpression) {
  // type(expression) in expression context
  auto r = Parse("module m;\n"
                 "  int a;\n"
                 "  initial begin $display(\"%s\", $typename(type(a))); end\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, TypeRefDataType) {
  // type(data_type) in expression context
  auto r = Parse(
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(logic [7:0]))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- incomplete_class_scoped_type ---
// type_identifier :: type_identifier_or_class_type
// (used within type_reference context for unresolved class scopes)

TEST(ParserA221, IncompleteClassScopedType) {
  // type(A::B) where A is used as a scope but may not be fully resolved
  auto r = Parse(
      "class outer;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin $display(\"%s\", $typename(type(outer::inner_t))); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
