

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(NetAndVariableTypeParsing, SigningSignedExplicit) {
  auto r = Parse("module m; logic signed x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(FirstItem(r)->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, SigningUnsignedExplicit) {
  auto r = Parse("module m; integer unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(FirstItem(r)->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, ImplicitDataTypeWithPackedDim) {
  auto r = Parse("module m(input [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_right, nullptr);
}

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
  auto r = Parse(
      "module m;\n"
      "  typedef union soft { int a; bit b; } u_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(FirstItem(r)->typedef_type.is_soft);
}

// data_type ::= ... struct_union [ packed [ signing ] ] { ... }  — the optional
// signing on a packed structure (`struct packed signed`), a distinct input form
// from the bare and plain-packed structures tested above.
TEST(NetAndVariableTypeParsing, StructUnionPackedSigned) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed signed { logic [3:0] a; } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_TRUE(item->typedef_type.is_signed);
}

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

TEST(NetAndVariableTypeParsing, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kString);
}

TEST(NetAndVariableTypeParsing, DataTypeChandle) {
  auto r = Parse("module m; chandle h; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kChandle);
}

TEST(NetAndVariableTypeParsing, DataTypeEvent) {
  auto r = Parse("module m; event e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FirstItem(r)->data_type.kind, DataTypeKind::kEvent);
}

TEST(NetAndVariableTypeParsing, TypeReferenceFromExpression) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  var type(x) y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  EXPECT_NE(mod->items[1]->data_type.type_ref_expr, nullptr);
}

TEST(NetAndVariableTypeParsing, VarDataTypeOnPort) {
  auto r = Parse("module m(input var int x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(NetAndVariableTypeParsing, StructWithExtraPackedDimensions) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] f; } s_t;\n"
      "  s_t [1:0][3:0] arr;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, CastingTypeIntegerAtom) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial x = int'(3.14);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, CastingTypeSigning) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] u;\n"
      "  logic [7:0] s;\n"
      "  initial s = signed'(u);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, CastingTypeUnsigned) {
  auto r = Parse(
      "module m;\n"
      "  logic signed [7:0] s;\n"
      "  logic [7:0] u;\n"
      "  initial u = unsigned'(s);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, CastingTypeString) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = string'(\"hello\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, CastingTypeConst) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int y;\n"
              "  initial y = const'(5);\n"
              "endmodule\n"));
}

TEST(NetAndVariableTypeParsing, VirtualInterfaceDataType) {
  auto r = Parse(
      "module m;\n"
      "  virtual interface my_if v;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "my_if");
}

TEST(NetAndVariableTypeParsing, VirtualInterfaceWithModport) {
  auto r = Parse(
      "module m;\n"
      "  virtual interface my_if.mp v;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "my_if");
  EXPECT_EQ(item->data_type.modport_name, "mp");
}

TEST(NetAndVariableTypeParsing, EnumBaseTypeIntegerVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [3:0] { A, B, C } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->typedef_type.enum_base_kind, DataTypeKind::kLogic);
}

TEST(NetAndVariableTypeParsing, EnumNameDeclarationWithRange) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { S[4] } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_GE(item->typedef_type.enum_members.size(), 1u);
  EXPECT_NE(item->typedef_type.enum_members[0].range_start, nullptr);
}

TEST(NetAndVariableTypeParsing, EnumNameDeclarationWithConstantExpression) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { RED = 1, GREEN = 2, BLUE = 4 } color_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_EQ(item->typedef_type.enum_members.size(), 3u);
  EXPECT_NE(item->typedef_type.enum_members[0].value, nullptr);
}

TEST(NetAndVariableTypeParsing, TypeReferenceFromDataType) {
  auto r = Parse(
      "module m;\n"
      "  var type(int) y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, ConstDataDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  const int x = 5;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, InterconnectImplicitNetPortType) {
  EXPECT_TRUE(
      ParseOk("module m(interconnect [3:0] bus);\n"
              "endmodule\n"));
}

TEST(NetAndVariableTypeParsing, ImplicitDataTypeSigningOnly) {
  auto r = Parse(
      "module m(input signed a);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, StructUnionMemberRandQualifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { rand int x; randc bit [1:0] y; } s_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_TRUE(item->typedef_type.struct_members[0].is_rand);
  EXPECT_TRUE(item->typedef_type.struct_members[1].is_randc);
}

TEST(NetAndVariableTypeParsing, ClassTypeAsDataType) {
  auto r = Parse(
      "class my_cls;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_cls h;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(mod->items[0]->data_type.type_name, "my_cls");
}

TEST(NetAndVariableTypeParsing, ClassTypeWithParameterValueAssignment) {
  auto r = Parse(
      "class my_cls #(int W = 8);\n"
      "  logic [W-1:0] x;\n"
      "endclass\n"
      "module m;\n"
      "  my_cls#(16) h;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(mod->items[0]->data_type.type_name, "my_cls");
  EXPECT_FALSE(mod->items[0]->data_type.type_params.empty());
}

TEST(NetAndVariableTypeParsing, EnumBaseTypeFromTypeIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] base_t;\n"
      "  typedef enum base_t { A, B, C } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, PackageScopedTypeIdentifierAsDataType) {
  auto r = Parse(
      "package p;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  p::byte_t b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(mod->items[0]->data_type.scope_name, "p");
  EXPECT_EQ(mod->items[0]->data_type.type_name, "byte_t");
}

TEST(NetAndVariableTypeParsing, CastingTypeConstantPrimaryWidth) {
  // The constant_primary alternative of casting_type — a width literal as the
  // cast's target type, e.g. 8'(x) reshapes x to eight bits.
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = 8'(a);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, ClassScopeTypeAccess) {
  auto r = Parse(
      "class outer;\n"
      "  typedef logic [3:0] inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  outer::inner_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// enum_base_type ::= integer_atom_type [ signing ] | ...  The integer_atom
// alternative (e.g. `enum int`), distinct from the integer_vector and
// type_identifier bases exercised above.
TEST(NetAndVariableTypeParsing, EnumBaseTypeIntegerAtom) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum int { A, B } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->typedef_type.enum_base_kind, DataTypeKind::kInt);
}

// enum_name_declaration ::= enum_identifier
//   [ [ integral_number [ : integral_number ] ] ] [ = constant_expression ]
// The two-bound range form (`X[0:3]`), distinct from the single-index `S[4]`.
TEST(NetAndVariableTypeParsing, EnumNameDeclarationRangeWithBounds) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { X[0:3] } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_GE(item->typedef_type.enum_members.size(), 1u);
  EXPECT_NE(item->typedef_type.enum_members[0].range_start, nullptr);
  EXPECT_NE(item->typedef_type.enum_members[0].range_end, nullptr);
}

// type_reference ::= type ( data_type_or_incomplete_class_scoped_type )  over a
// class-scoped type name (`type(c::inner_t)`), exercising the scoped
// alternative of data_type_or_incomplete_class_scoped_type rather than a bare
// data_type.
TEST(NetAndVariableTypeParsing, TypeReferenceClassScopedType) {
  auto r = Parse(
      "class c;\n"
      "  typedef logic [3:0] inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  var type(c::inner_t) y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->data_type.type_ref_expr, nullptr);
}

// var_data_type ::= data_type | var data_type_or_implicit  — the implicit
// alternative: `var` followed by only a signing and a packed dimension, no
// explicit data_type (contrast with `var int` above).
TEST(NetAndVariableTypeParsing, VarDataTypeImplicitSignedPacked) {
  auto r = Parse("module m(input var signed [3:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].has_explicit_var);
  EXPECT_TRUE(mod->ports[0].data_type.is_signed);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

// casting_type ::= simple_type | ...  The simple_type alternative admits a
// non_integer_type (`real`), a different keyword-cast path than the integer
// atom `int'` exercised above.
TEST(NetAndVariableTypeParsing, CastingTypeNonIntegerType) {
  auto r = Parse(
      "module m;\n"
      "  real r;\n"
      "  initial r = real'(5);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// casting_type simple_type ::= ... | ps_type_identifier  — a user-defined type
// name as the cast target (`my_t'(...)`), routed through the identifier-cast
// path rather than the keyword-cast path.
TEST(NetAndVariableTypeParsing, CastingTypeUserDefinedType) {
  auto r = Parse(
      "module m;\n"
      "  typedef int my_t;\n"
      "  my_t v;\n"
      "  initial v = my_t'(3);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// enum_base_type ::= integer_atom_type [ signing ] | ...  The optional signing
// on an integer_atom base (`enum int unsigned`).
TEST(NetAndVariableTypeParsing, EnumBaseTypeIntegerAtomWithSigning) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum int unsigned { A, B } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.enum_base_kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->typedef_type.is_signed);
}

// enum_base_type ::= ... | integer_vector_type [ signing ] [ packed_dimension ]
// The optional signing on an integer_vector base (`enum logic signed [3:0]`).
TEST(NetAndVariableTypeParsing, EnumBaseTypeIntegerVectorWithSigning) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic signed [3:0] { A, B } e_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.enum_base_kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->typedef_type.is_signed);
}

// NEGATIVE: struct_union ::= struct | union [ soft | tagged ] permits at most
// one qualifier on a union; `union soft tagged` violates that structure and
// must be rejected.
TEST(NetAndVariableTypeParsing, UnionRejectsBothSoftAndTagged) {
  auto r = Parse(
      "module m;\n"
      "  typedef union soft tagged { int a; bit b; } u_t;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

// interface_class_type ::= ps_class_identifier [ parameter_value_assignment ]
// This production appears in a class's implements clause; the parameterized
// form exercises both the class identifier and the optional
// parameter_value_assignment in one shot. Built from real class syntax but
// observing THIS production's parse.
TEST(NetAndVariableTypeParsing, InterfaceClassTypeInImplementsClause) {
  auto r = Parse(
      "interface class I #(int W = 1);\n"
      "endclass\n"
      "class C implements I #(8);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 2u);
  auto* c = r.cu->classes[1];
  ASSERT_GE(c->implements_types.size(), 1u);
  EXPECT_EQ(c->implements_types[0].name, "I");
  EXPECT_FALSE(c->implements_types[0].type_params.empty());
}

}  // namespace
