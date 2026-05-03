#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- integer_vector_type ::= bit | logic | reg ---

TEST(NetAndVariableTypeParsing, IntegerVectorTypes) {
  auto r = Parse(
      "module m;\n"
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

TEST(NetAndVariableTypeParsing, IntegerVectorWithSigningAndDim) {
  auto r = Parse("module m; logic signed [7:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(dt.is_signed);
  EXPECT_NE(dt.packed_dim_left, nullptr);
}

// --- integer_atom_type ::= byte | shortint | int | longint | integer | time ---

TEST(NetAndVariableTypeParsing, IntegerAtomTypes) {
  auto r = Parse(
      "module m;\n"
      "  byte a;\n"
      "  shortint b;\n"
      "  int c;\n"
      "  longint d;\n"
      "  integer e;\n"
      "  time f;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(items[5]->data_type.kind, DataTypeKind::kTime);
}

TEST(NetAndVariableTypeParsing, IntegerAtomWithSigning) {
  auto r = Parse("module m; byte unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kByte);
  EXPECT_FALSE(dt.is_signed);
}

// --- non_integer_type ::= shortreal | real | realtime ---

TEST(NetAndVariableTypeParsing, NonIntegerTypes) {
  auto r = Parse(
      "module m;\n"
      "  shortreal a;\n"
      "  real b;\n"
      "  realtime c;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kRealtime);
}

// --- data_type: string, chandle, event ---

TEST(NetAndVariableTypeParsing, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}

TEST(NetAndVariableTypeParsing, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kChandle);
}

TEST(NetAndVariableTypeParsing, DataTypeEvent) {
  auto r = Parse("module m; event e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEvent);
}

// --- data_type: enum ---

TEST(NetAndVariableTypeParsing, DataTypeEnum) {
  auto r = Parse("module m; enum {A, B, C} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEnum);
}

// --- data_type: struct_union ---

TEST(NetAndVariableTypeParsing, StructUnionStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kStruct);
}

TEST(NetAndVariableTypeParsing, StructUnionUnion) {
  auto r = Parse(
      "module m;\n"
      "  union { int a; int b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kUnion);
}

TEST(NetAndVariableTypeParsing, StructUnionUnionTagged) {
  auto r = Parse(
      "module m;\n"
      "  union tagged { int a; int b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(dt.is_tagged);
}

TEST(NetAndVariableTypeParsing, StructUnionUnionSoft) {
  auto r = Parse(
      "module m;\n"
      "  union soft { int a; int b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(dt.is_soft);
}

TEST(NetAndVariableTypeParsing, StructPackedSigned) {
  auto r = Parse(
      "module m;\n"
      "  struct packed signed { logic [7:0] a; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(dt.is_packed);
  EXPECT_TRUE(dt.is_signed);
}

// --- struct_union_member: {attribute_instance} [random_qualifier]
//     data_type_or_void list_of_variable_decl_assignments ; ---

TEST(NetAndVariableTypeParsing, StructMemberWithRand) {
  auto r = Parse(
      "module m;\n"
      "  struct { rand int a; randc int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0].is_rand);
  EXPECT_TRUE(members[1].is_randc);
}

TEST(NetAndVariableTypeParsing, StructMemberVoid) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  struct { void a; } s;\n"
      "endmodule"));
}

// --- data_type: [class_scope | package_scope] type_identifier ---

TEST(NetAndVariableTypeParsing, DataTypeClassType) {
  auto r = Parse(
      "class my_cls;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m; my_cls::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, DataTypePackageScope) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int my_type;\n"
      "endpackage\n"
      "module m; pkg::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kNamed);
  EXPECT_EQ(dt.scope_name, "pkg");
  EXPECT_EQ(dt.type_name, "my_type");
}

// --- class_type: ps_class_identifier [#(params)] {:: class_identifier [#(params)]} ---

TEST(NetAndVariableTypeParsing, ClassTypeParameterized) {
  auto r = Parse(
      "class my_cls #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module m; my_cls#(logic)::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- data_type: type_reference ---

TEST(NetAndVariableTypeParsing, TypeReferenceExpression) {
  // §6.8 footnote 18 requires the var keyword when type_reference is the
  // data type of a variable declaration.
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  var type(x) y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, TypeReferenceDataType) {
  // §6.8 footnote 18 requires the var keyword when type_reference is the
  // data type of a variable declaration.
  auto r = Parse(
      "module m;\n"
      "  var type(int) y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- enum_base_type ---

TEST(NetAndVariableTypeParsing, EnumBaseAtomType) {
  auto r = Parse("module m; enum int {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEnum);
}

TEST(NetAndVariableTypeParsing, EnumBaseVectorWithDim) {
  auto r = Parse("module m; enum logic [3:0] {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- enum_name_declaration ---

TEST(NetAndVariableTypeParsing, EnumNameWithRange) {
  auto r = Parse("module m; enum {A[3]} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, EnumNameWithRangeAndValue) {
  auto r = Parse("module m; enum {A[2:0] = 5} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- net_type ---

TEST(NetAndVariableTypeParsing, NetTypeVariants) {
  auto r = Parse(
      "module m;\n"
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
  auto& items = r.cu->modules[0]->items;
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

TEST(NetAndVariableTypeParsing, NetPortTypeWithNetType) {
  auto r = Parse("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

// --- variable_port_type / var_data_type ---

TEST(NetAndVariableTypeParsing, VarDataTypeWithVar) {
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(NetAndVariableTypeParsing, VarDataTypeImplicit) {
  EXPECT_TRUE(ParseOk("module m(input var [7:0] d); endmodule"));
}

// --- signing ---

TEST(NetAndVariableTypeParsing, SigningSigned) {
  auto r = Parse("module m; logic signed [7:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, SigningUnsigned) {
  auto r = Parse("module m; logic unsigned [7:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

// --- implicit_data_type ---

TEST(NetAndVariableTypeParsing, ImplicitDataTypeSigning) {
  auto r = Parse("module m; wire signed [7:0] w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, ImplicitDataTypePackedDim) {
  auto r = Parse("module m; wire [15:0] w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->items[0]->data_type.packed_dim_left, nullptr);
}

// --- incomplete_class_scoped_type ---

TEST(NetAndVariableTypeParsing, IncompleteClassScopedType) {
  auto r = Parse(
      "class A;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; A::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kNamed);
  EXPECT_EQ(dt.scope_name, "A");
  EXPECT_EQ(dt.type_name, "inner_t");
}

// --- data_type_or_void ---

TEST(NetAndVariableTypeParsing, DataTypeOrVoidReturn) {
  auto r = Parse(
      "module m;\n"
      "  function void f(); endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Edge cases ---

TEST(NetAndVariableTypeParsing, DataTypeNonInteger) {
  auto r = Parse("module m; real x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kReal);
}

TEST(NetAndVariableTypeParsing, IntegerVectorMultiplePackedDims) {
  auto r = Parse("module m; logic [7:0][3:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, EnumPackedDimension) {
  EXPECT_TRUE(ParseOk("module m; enum logic [1:0] {A, B, C} x; endmodule"));
}

// --- struct_union_member: {attribute_instance} ---

TEST(NetAndVariableTypeParsing, StructMemberWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  struct { (* mark *) int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  ASSERT_FALSE(members[0].attrs.empty());
  EXPECT_EQ(members[0].attrs[0].name, "mark");
}

// --- struct_union_member: multiple names in list_of_variable_decl_assignments ---

TEST(NetAndVariableTypeParsing, StructMemberMultipleNames) {
  auto r = Parse(
      "module m;\n"
      "  struct { int a, b, c; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_EQ(members[0].name, "a");
  EXPECT_EQ(members[1].name, "b");
  EXPECT_EQ(members[2].name, "c");
}

// --- class_type: chained :: scope resolution ---

TEST(NetAndVariableTypeParsing, ClassTypeChainedScope) {
  auto r = Parse(
      "class A;\n"
      "  class B;\n"
      "    typedef int inner_t;\n"
      "  endclass\n"
      "endclass\n"
      "module m; A::B::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kNamed);
  EXPECT_EQ(dt.scope_name, "B");
  EXPECT_EQ(dt.type_name, "inner_t");
}

// --- enum_base_type: type_identifier ---

TEST(NetAndVariableTypeParsing, EnumBaseTypeIdentifier) {
  auto r = Parse(
      "typedef logic [3:0] nibble_t;\n"
      "module m; enum nibble_t {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEnum);
}

// --- struct packed unsigned ---

TEST(NetAndVariableTypeParsing, StructPackedUnsigned) {
  auto r = Parse(
      "module m;\n"
      "  struct packed unsigned { logic [7:0] a; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(dt.is_packed);
  EXPECT_FALSE(dt.is_signed);
}

// --- error: empty enum body ---

TEST(NetAndVariableTypeParsing, EnumEmptyBodyIsError) {
  auto r = Parse("module m; enum {} x; endmodule");
  EXPECT_TRUE(r.has_errors);
}

// --- named type with packed dimensions ---

TEST(NetAndVariableTypeParsing, NamedTypeWithPackedDim) {
  auto r = Parse(
      "typedef logic [7:0] byte_t;\n"
      "module m; byte_t [3:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kNamed);
  EXPECT_NE(dt.packed_dim_left, nullptr);
}

// --- struct/enum with trailing packed_dimension ---

TEST(NetAndVariableTypeParsing, StructWithTrailingPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { logic [7:0] a; } [3:0] arr;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kStruct);
  EXPECT_NE(dt.packed_dim_left, nullptr);
}

TEST(NetAndVariableTypeParsing, EnumWithTrailingPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  enum logic [1:0] {A, B, C} [3:0] arr;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- enum member inside struct ---

TEST(NetAndVariableTypeParsing, StructMemberWithEnumType) {
  auto r = Parse(
      "module m;\n"
      "  struct { enum {A, B} x; int y; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kEnum);
}

}  // namespace
