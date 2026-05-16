// §A.2.2.1: parser-stage coverage of Net and variable types. The BNF rules
// covered here are: data_type, data_type_or_implicit, implicit_data_type,
// integer_atom_type, integer_vector_type, non_integer_type, net_type,
// signing, simple_type, struct_union, struct_union_member, data_type_or_void,
// type_reference, and var_data_type.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.2.2.1 integer_vector_type ::= bit | logic | reg — each terminal selects
// the corresponding DataTypeKind in a variable declaration.
TEST(NetAndVariableTypeParsing, IntegerVectorTypeLogic) {
  auto r = Parse("module m; logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
}

TEST(NetAndVariableTypeParsing, IntegerVectorTypeBit) {
  auto r = Parse("module m; bit x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kBit);
}

TEST(NetAndVariableTypeParsing, IntegerVectorTypeReg) {
  auto r = Parse("module m; reg x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kReg);
}

// §A.2.2.1 integer_atom_type ::= byte | shortint | int | longint | integer |
// time — each maps to the matching DataTypeKind.
TEST(NetAndVariableTypeParsing, IntegerAtomByte) {
  auto r = Parse("module m; byte x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kByte);
}

TEST(NetAndVariableTypeParsing, IntegerAtomShortint) {
  auto r = Parse("module m; shortint x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kShortint);
}

TEST(NetAndVariableTypeParsing, IntegerAtomInt) {
  auto r = Parse("module m; int x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kInt);
}

TEST(NetAndVariableTypeParsing, IntegerAtomLongint) {
  auto r = Parse("module m; longint x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kLongint);
}

TEST(NetAndVariableTypeParsing, IntegerAtomInteger) {
  auto r = Parse("module m; integer x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kInteger);
}

TEST(NetAndVariableTypeParsing, IntegerAtomTime) {
  auto r = Parse("module m; time x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTime);
}

// §A.2.2.1 non_integer_type ::= shortreal | real | realtime — each maps to
// its DataTypeKind.
TEST(NetAndVariableTypeParsing, NonIntegerTypeReal) {
  auto r = Parse("module m; real x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kReal);
}

TEST(NetAndVariableTypeParsing, NonIntegerTypeShortreal) {
  auto r = Parse("module m; shortreal x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kShortreal);
}

TEST(NetAndVariableTypeParsing, NonIntegerTypeRealtime) {
  auto r = Parse("module m; realtime x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kRealtime);
}

// §A.2.2.1 net_type ::= supply0 | supply1 | tri | triand | trior | trireg |
// tri0 | tri1 | uwire | wire | wand | wor — each net keyword is recognized
// and produces a net declaration.
TEST(NetAndVariableTypeParsing, NetTypeWire) {
  auto r = Parse("module m; wire w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kWire);
}

TEST(NetAndVariableTypeParsing, NetTypeTri) {
  auto r = Parse("module m; tri w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTri);
}

TEST(NetAndVariableTypeParsing, NetTypeWand) {
  auto r = Parse("module m; wand w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kWand);
}

TEST(NetAndVariableTypeParsing, NetTypeWor) {
  auto r = Parse("module m; wor w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kWor);
}

TEST(NetAndVariableTypeParsing, NetTypeTriand) {
  auto r = Parse("module m; triand w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTriand);
}

TEST(NetAndVariableTypeParsing, NetTypeTrior) {
  auto r = Parse("module m; trior w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTrior);
}

TEST(NetAndVariableTypeParsing, NetTypeTri0) {
  auto r = Parse("module m; tri0 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTri0);
}

TEST(NetAndVariableTypeParsing, NetTypeTri1) {
  auto r = Parse("module m; tri1 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTri1);
}

TEST(NetAndVariableTypeParsing, NetTypeTrireg) {
  auto r = Parse("module m; trireg w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kTrireg);
}

TEST(NetAndVariableTypeParsing, NetTypeUwire) {
  auto r = Parse("module m; uwire w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kUwire);
}

TEST(NetAndVariableTypeParsing, NetTypeSupply0) {
  auto r = Parse("module m; supply0 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kSupply0);
}

TEST(NetAndVariableTypeParsing, NetTypeSupply1) {
  auto r = Parse("module m; supply1 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kSupply1);
}

// §A.2.2.1 signing ::= signed | unsigned — explicit signing on a type
// overrides the default for that DataTypeKind.
TEST(NetAndVariableTypeParsing, SigningSignedExplicit) {
  auto r = Parse("module m; logic signed x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(FirstItem(r)->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, SigningUnsignedExplicit) {
  // §A.2.2.1: integer is signed by default; explicit `unsigned` overrides.
  auto r = Parse("module m; integer unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(FirstItem(r)->data_type.is_signed);
}

// §A.2.2.1 implicit_data_type ::= [signing] {packed_dimension} — a declaration
// that omits the leading type keyword parses with kImplicit and the dimensions
// are attached.
TEST(NetAndVariableTypeParsing, ImplicitDataTypeWithPackedDim) {
  // §A.2.1.2 input_declaration takes a net_port_type whose
  // data_type_or_implicit permits the implicit form. The leading [7:0] is
  // parsed by ParsePackedDims.
  auto r = Parse("module m(input [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_right, nullptr);
}

// §A.2.2.1 struct_union ::= struct | union [ tagged | soft ] — the parser
// records the qualifier on the resulting DataType.
TEST(NetAndVariableTypeParsing, StructUnionStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
}

TEST(NetAndVariableTypeParsing, StructUnionUnion) {
  auto r = Parse(
      "module m;\n"
      "  typedef union { int a; bit b; } u_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->typedef_type.kind, DataTypeKind::kUnion);
}

TEST(NetAndVariableTypeParsing, StructUnionTagged) {
  // §A.2.2.1: struct_union ::= ... | union [ tagged ] — the `tagged`
  // qualifier on a union is recorded on the DataType.
  auto r = Parse(
      "module m;\n"
      "  typedef union tagged { int a; bit b; } u_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
}

TEST(NetAndVariableTypeParsing, StructUnionSoft) {
  // §A.2.2.1: struct_union ::= ... | union [ soft ]
  auto r = Parse(
      "module m;\n"
      "  typedef union soft { int a; bit b; } u_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(FirstItem(r)->typedef_type.is_soft);
}

// §A.2.2.1 struct_union_member with multiple comma-separated identifiers in
// a single data_type — the BNF lists struct_union_member as one production
// that may declare more than one member name per data_type.
TEST(NetAndVariableTypeParsing, StructUnionMemberMultipleNames) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a, b, c; } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "a");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "b");
  EXPECT_EQ(item->typedef_type.struct_members[2].name, "c");
}

// §A.2.2.1 data_type_or_void ::= data_type | void — void is admitted as a
// struct_union_member's type (used by the tagged-union "void member" form).
TEST(NetAndVariableTypeParsing, DataTypeOrVoidInTaggedUnion) {
  auto r = Parse(
      "module m;\n"
      "  typedef union tagged { void none; int some; } u_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_GE(item->typedef_type.struct_members.size(), 1u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kVoid);
}

// §A.2.2.1 data_type ::= ... | string — the string keyword stands as a
// data_type alternative on its own.
TEST(NetAndVariableTypeParsing, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kString);
}

// §A.2.2.1 data_type ::= ... | chandle
TEST(NetAndVariableTypeParsing, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kChandle);
}

// §A.2.2.1 data_type ::= ... | event
TEST(NetAndVariableTypeParsing, DataTypeEvent) {
  auto r = Parse("module m; event e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kEvent);
}

// §A.2.2.1 type_reference ::= type ( expression ) — a type(expr) reference
// can stand in for a data_type in a variable declaration.
TEST(NetAndVariableTypeParsing, TypeReferenceFromExpression) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  type(x) y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The second item carries a non-null type_ref_expr captured by
  // TryParseTypeRef.
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  EXPECT_NE(mod->items[1]->data_type.type_ref_expr, nullptr);
}

// §A.2.2.1 var_data_type ::= data_type | var data_type_or_implicit — the
// `var` keyword in a variable port type is admitted.
TEST(NetAndVariableTypeParsing, VarDataTypeOnPort) {
  auto r = Parse("module m(input var int x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.2.2.1 simple_type ::= integer_type | non_integer_type | ps_type_identifier
// | ps_parameter_identifier — a user-defined typedef name is a
// ps_type_identifier and stands as a simple_type in a variable declaration.
TEST(NetAndVariableTypeParsing, SimpleTypeUserDefined) {
  auto r = Parse(
      "module m;\n"
      "  typedef int word_t;\n"
      "  word_t w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  EXPECT_EQ(mod->items[1]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(mod->items[1]->data_type.type_name, "word_t");
}

// §A.2.2.1 ↔ §A.9.1 cross-link: struct_union_member ::=
// { attribute_instance } [ random_qualifier ] data_type_or_void ... — the
// attribute_instance from §A.9.1 sits as a member prefix and the parser must
// attach it to the resulting StructMember.
TEST(NetAndVariableTypeParsing, StructUnionMemberCarriesAttributeInstance) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {\n"
      "    (* keep *) int a;\n"
      "  } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 1u);
  ASSERT_GE(item->typedef_type.struct_members[0].attrs.size(), 1u);
  EXPECT_EQ(item->typedef_type.struct_members[0].attrs[0].name, "keep");
}

// §A.2.2.1 ↔ §A.9.1 cross-link: an attr_spec value is a §A.8.3
// constant_expression. The expression is parsed by the §A.8.3 expression
// machinery — the cross-link shows up in the value's ExprKind.
TEST(NetAndVariableTypeParsing,
     StructUnionMemberAttributeInstanceConstExprValue) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {\n"
      "    (* weight = 2 + 3 *) int x;\n"
      "  } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 1u);
  ASSERT_GE(item->typedef_type.struct_members[0].attrs.size(), 1u);
  auto& a = item->typedef_type.struct_members[0].attrs[0];
  EXPECT_EQ(a.name, "weight");
  ASSERT_NE(a.value, nullptr);
  EXPECT_EQ(a.value->kind, ExprKind::kBinary);
}

// §A.2.2.1 ↔ §A.8.3 cross-link: the packed_dimension list inside a data_type
// uses §A.8.3 constant_expression bounds. The parser threads ParseExpr through
// ParsePackedDims, so a binary constant_expression appears in the bound slot.
TEST(NetAndVariableTypeParsing, PackedDimensionUsesConstantExpression) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 4;\n"
      "  logic [N-1:0] x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  auto& dt = mod->items[1]->data_type;
  ASSERT_NE(dt.packed_dim_left, nullptr);
  EXPECT_EQ(dt.packed_dim_left->kind, ExprKind::kBinary);
  ASSERT_NE(dt.packed_dim_right, nullptr);
  EXPECT_EQ(dt.packed_dim_right->kind, ExprKind::kIntegerLiteral);
}

// §A.2.2.1 data_type ::= struct_union ... { packed_dimension } — multiple
// packed_dimensions chain on a struct type.
TEST(NetAndVariableTypeParsing, StructWithExtraPackedDimensions) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] f; } s_t;\n"
      "  s_t [1:0][3:0] arr;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
