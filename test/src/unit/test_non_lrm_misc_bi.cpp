// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static void VerifyEnumMemberNames(const std::vector<EnumMember>& members,
                                  const std::string expected[], size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
  }
}

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult6& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

namespace {

// string
TEST(ParserA221, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}

// --- Named event tests ---
TEST(Parser, EventDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item->name, "ev");
}

// event
TEST(ParserA221, DataTypeEvent) {
  auto r = Parse("module m; event ev; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEvent);
}

TEST(Parser, TypedefEnum) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { A, B, C } state_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "state_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  std::string expected[] = {"A", "B", "C"};
  VerifyEnumMemberNames(item->typedef_type.enum_members, expected,
                        std::size(expected));
}

TEST(Parser, EnumWithValues) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { IDLE=0, RUN=1, STOP=2 } cmd_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  std::string expected[] = {"IDLE", "RUN", "STOP"};
  ASSERT_EQ(members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
    EXPECT_NE(members[i].value, nullptr) << "member " << i;
  }
}

TEST(Parser, InlineEnumVar) {
  auto r = Parse(
      "module t;\n"
      "  enum { X, Y } my_var;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "my_var");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(item->data_type.enum_members.size(), 2);
}

// 23. Enum in module scope
TEST(ParserClause03, Cl3_13_EnumInModuleScope) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
      "  state_t current_state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_typedef = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      found_typedef = true;
      EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
    }
  }
  EXPECT_TRUE(found_typedef);
}

// enum [enum_base_type] { ... } {packed_dimension}
TEST(ParserA221, DataTypeEnum) {
  auto r = Parse("module m; enum logic [1:0] {A, B, C} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
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
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "  enum nibble_t {A, B} x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 27. Parameter and localparam in module scope
TEST(ParserClause03, Cl3_13_ParameterAndLocalparamInModule) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_param = false;
  bool found_localparam = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "WIDTH")
      found_param = true;
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "DEPTH")
      found_localparam = true;
  }
  EXPECT_TRUE(found_param);
  EXPECT_TRUE(found_localparam);
}

// parameter_port_list: data_type list_of_param_assignments (no keyword)
TEST(SourceText, ParamPortDataTypeForm) {
  auto r = Parse("module m #(int WIDTH = 8); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "WIDTH");
}

// parameter_port_list: mixed forms
TEST(SourceText, ParamPortMixedForms) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 2,\n"
      "           type T = logic, int C = 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
  EXPECT_EQ(r.cu->modules[0]->params[2].first, "T");
  EXPECT_EQ(r.cu->modules[0]->params[3].first, "C");
}

TEST(ParserAnnexA, A2ParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 16;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kParamDecl);
}

// --- list_of_param_assignments ---
// param_assignment { , param_assignment }
TEST(ParserA23, ListOfParamAssignmentsSingle) {
  auto r = Parse("module m; parameter int A = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserA23, ListOfParamAssignmentsMultiple) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA24, ParamAssignmentNoDefault) {
  // Parameter in module header without default
  auto r = Parse("module m #(parameter int P); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- specparam_assignment ---
// specparam_identifier = constant_mintypmax_expression
// | pulse_control_specparam
TEST(ParserA24, SpecparamAssignmentBasic) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- type_assignment ---
// type_identifier [ = data_type_or_incomplete_class_scoped_type ]
TEST(ParserA24, TypeAssignmentWithDefault) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

// parameter_port_list: type parameter (#(type T = int))
TEST(SourceText, ParamPortTypeParameter) {
  auto r = Parse("module m #(type T = int); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

// --- list_of_type_assignments ---
// type_assignment { , type_assignment }
TEST(ParserA23, ListOfTypeAssignmentsSingle) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserA24, TypeAssignmentNoDefault) {
  auto r = Parse("module m #(parameter type T); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, TypeAssignmentComplexType) {
  auto r = Parse("module m; parameter type T = logic [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// parameter_port_list with localparam (parameter_port_declaration form 2)
TEST(SourceText, ParamPortLocalparam) {
  auto r = Parse("module m #(localparam int X = 5); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "X");
}

TEST(ParserA24, LocalparamAssignment) {
  auto r = Parse("module m; localparam int LP = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "LP");
}

// §A.2.8 block_item_declaration alternative 2: local_parameter_declaration
TEST(ParserA28, LocalparamInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int X = 5;\n"
      "    $display(\"%0d\", X);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "X");
}

// =========================================================================
// §6.5-6.7: Net declarations
// =========================================================================
TEST(ParserSection6, WireDeclaration_Kind) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
}

TEST(ParserSection6, WireDeclaration_Props) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(ParserSection6, TriDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  tri [3:0] t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

// =========================================================================
// §6.8: Variable declarations
// =========================================================================
TEST(ParserSection6, LogicVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserSection6, IntVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "count");
}

TEST(ParserSection6, ByteVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
}

TEST(ParserSection6, LongintVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
}

// =========================================================================
// §6.9: Vector declarations
// =========================================================================
TEST(ParserSection6, SignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [7:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(ParserSection6, UnsignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic unsigned [15:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "uv");
}

TEST(ParserSection6, VectorWithMultipleDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "mem");
}

// =========================================================================
// §6.11.3: Default signedness per Table 6-8
// =========================================================================
TEST(ParserSection6, IntDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed) << "int is signed by default";
}

TEST(ParserSection6, IntExplicitUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  int unsigned x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed) << "int unsigned is unsigned";
}

TEST(ParserSection6, ByteDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_TRUE(item->data_type.is_signed) << "byte is signed by default";
}

TEST(ParserSection6, ShortintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  shortint s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_TRUE(item->data_type.is_signed) << "shortint is signed by default";
}

TEST(ParserSection6, LongintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  longint l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_TRUE(item->data_type.is_signed) << "longint is signed by default";
}

TEST(ParserSection6, IntegerDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  integer i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(item->data_type.is_signed) << "integer is signed by default";
}

TEST(ParserSection6, TimeDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_FALSE(item->data_type.is_signed) << "time is unsigned by default";
}

TEST(ParserSection6, LogicDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  logic l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed) << "logic is unsigned by default";
}

TEST(ParserSection6, BitDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  bit b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(item->data_type.is_signed) << "bit is unsigned by default";
}

TEST(ParserSection6, RegDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed) << "reg is unsigned by default";
}

// =========================================================================
// §6.12: Real, shortreal, and realtime data types
// =========================================================================
TEST(ParserSection6, RealVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
}

TEST(ParserSection6, ShortrealVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  shortreal sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
}

TEST(ParserSection6, RealtimeVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  realtime rt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
}

// =========================================================================
// §6.13: Void data type
// =========================================================================
TEST(ParserSection6, VoidFunctionReturn) {
  auto r = Parse(
      "module t;\n"
      "  function void do_nothing();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// =========================================================================
// §6.14: Chandle data type
// =========================================================================
TEST(ParserSection6, ChandleVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(item->name, "ch");
}

// =========================================================================
// §6.17: Event data type
// =========================================================================
TEST(ParserSection6, EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
}

// =========================================================================
// §6.18: User-defined types (typedef)
// =========================================================================
TEST(ParserSection6, TypedefInt) {
  auto r = Parse(
      "module t;\n"
      "  typedef int myint;\n"
      "  myint x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "myint");
}

// =========================================================================
// §6.19: Enumerations
// =========================================================================
TEST(ParserSection6, EnumBasic) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
}

// =========================================================================
// §6.20: Constants
// =========================================================================
TEST(ParserSection6, ConstVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ParserSection6, ConstVarDecl_NameAndInit) {
  auto r = Parse(
      "module t;\n"
      "  const logic [7:0] MAX = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "MAX");
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, ConstIntDecl) {
  auto r = Parse(
      "module t;\n"
      "  const int LIMIT = 100;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_const);
}

// =========================================================================
// §6.21: Scope and lifetime
// =========================================================================
TEST(ParserSection6, AutomaticVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  function automatic int get_val();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, StaticFunction) {
  auto r = Parse(
      "module t;\n"
      "  function static int counter();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_static);
}

// =========================================================================
// §6.24: Casting
// =========================================================================
TEST(ParserSection6, IntCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

TEST(ParserSection6, IntCast_Details) {
  auto r = Parse(
      "module t;\n"
      "  initial x = int'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->text, "int");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(ParserSection6, SignedCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = signed'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "signed");
}

TEST(ParserSection6, ConstCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = const'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "const");
}

// =========================================================================
// §6.24.1 -- Static casting (additional tests)
// =========================================================================
// =========================================================================
// §6.24.2 -- Dynamic casting ($cast)
// =========================================================================
TEST(ParserSection6, DynamicCastCall) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$cast");
}

TEST(ParserSection6, DynamicCastInCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ($cast(d, b))\n"
      "      $display(\"cast ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ParserSection6, DynamicCastAssignResult) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int ok;\n"
      "    ok = $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =========================================================================
// §6.24.3 -- Bit-stream casting
// =========================================================================
TEST(ParserSection6, BitStreamCastToType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    p = pair_t'(8'hAB);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastFromStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    logic [7:0] flat;\n"
      "    flat = logic [7:0]'(p);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastStreaming) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    byte a;\n"
      "    int b;\n"
      "    b = int'({<< byte {a}});\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =========================================================================
// §6.15: Class
// =========================================================================
TEST(ParserSection6, ClassVarDecl_ClassParsed) {
  // Class declared at top-level, then used as a type inside a module.
  auto r = Parse(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  MyClass obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->classes.empty());
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
  ASSERT_FALSE(r.cu->modules.empty());
}

}  // namespace
