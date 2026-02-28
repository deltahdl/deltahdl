// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Returns the first class member of kind kMethod, or nullptr if not found.
static ClassMember* FindMethodMember(ClassDecl* cls) {
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      return m;
    }
  }
  return nullptr;
}

namespace {

// 22. Struct in conditional expression (ternary).
TEST(ParserSection7, Sec7_2_2_StructTernary) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y, z;\n"
      "  logic sel;\n"
      "  initial z = sel ? x : y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// 23. Struct variable declaration with initializer in initial block.
TEST(ParserSection7, Sec7_2_2_VarDeclWithInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p = '{5, 10};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "p");
  ASSERT_NE(stmt->var_init, nullptr);
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kAssignmentPattern);
}

// 24. Struct assigned in for loop body.
TEST(ParserSection7, Sec7_2_2_AssignInForLoop) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int idx; int val; } entry_t;\n"
              "  entry_t table[4];\n"
              "  initial begin\n"
              "    for (int i = 0; i < 4; i = i + 1) begin\n"
              "      table[i] = '{i, i * 10};\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// 25. Struct with packed array member assigned.
TEST(ParserSection7, Sec7_2_2_PackedArrayMemberAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    logic [7:0] data;\n"
      "    logic [3:0] tag;\n"
      "  } tagged_data_t;\n"
      "  tagged_data_t td;\n"
      "  initial begin\n"
      "    td.data = 8'hFF;\n"
      "    td.tag = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(s1->lhs->kind, ExprKind::kMemberAccess);
}

// 26. Struct output port assigned in module body.
TEST(ParserSection7, Sec7_2_2_StructOutputPort) {
  EXPECT_TRUE(
      ParseOk("module t(\n"
              "  output logic [15:0] result\n"
              ");\n"
              "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
              "  s_t s;\n"
              "  assign s = 16'hDEAD;\n"
              "  assign result = s;\n"
              "endmodule\n"));
}

// 27. Positional assignment pattern elements count.
TEST(ParserSection7, Sec7_2_2_PositionalPatternElements) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } tri_t;\n"
      "  tri_t v;\n"
      "  initial v = '{100, 200, 300};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
  EXPECT_TRUE(stmt->rhs->pattern_keys.empty());
}

// 28. Packed struct assigned from bit vector and used in expression.
TEST(ParserSection7, Sec7_2_2_PackedStructBitVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] upper;\n"
      "    logic [3:0] lower;\n"
      "  } nibbles_t;\n"
      "  nibbles_t n;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    n = 8'b1010_0101;\n"
      "    result = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  ASSERT_NE(s0, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(s0->rhs, nullptr);
  EXPECT_EQ(s0->rhs->kind, ExprKind::kIntegerLiteral);
}

// 29. Named pattern keys verified for three-member struct.
TEST(ParserSection7, Sec7_2_2_NamedPatternKeysThreeMembers) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; int z; } vec3_t;\n"
      "  vec3_t v;\n"
      "  initial v = '{x: 1, y: 2, z: 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 3u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "x");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "y");
  EXPECT_EQ(stmt->rhs->pattern_keys[2], "z");
  ASSERT_EQ(stmt->rhs->elements.size(), 3u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kIntegerLiteral);
}

// 30. Multiple struct variables with different initializers.
TEST(ParserSection7, Sec7_2_2_MultipleVarsWithInit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p1 = '{1, 2};\n"
              "  pair_t p2 = '{3, 4};\n"
              "  pair_t p3 = '{default: 0};\n"
              "endmodule\n"));
}

// --- Class tests ---
TEST(Parser, EmptyClass) {
  auto r = Parse("class empty_cls; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "empty_cls");
  EXPECT_FALSE(r.cu->classes[0]->is_virtual);
}

// class_item ::= { attribute_instance } class_declaration (nested class)
TEST(SourceText, ClassNestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(members[0]->nested_class->name, "Inner");
}

// class_item ::= local_parameter_declaration ; | parameter_declaration ;
TEST(SourceText, ClassParameters) {
  auto r = Parse(
      "class C;\n"
      "  localparam int LP = 10;\n"
      "  parameter int P = 20;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kProperty);
}

// class_item ::= ; (empty statement)
TEST(SourceText, ClassEmptyItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  // Empty semicolons are consumed, only real members remain.
  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u);
}

// 30. Nested class (class within a module -- class in module scope)
TEST(ParserClause03, Cl3_13_NestedClassInModule) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class inner_cls;\n"
              "    int value;\n"
              "    function void set(int v);\n"
              "      value = v;\n"
              "    endfunction\n"
              "  endclass\n"
              "endmodule\n"));
}

// 12. Class scope -- members in class name space
TEST(ParserClause03, Cl3_13_ClassScopeMembers) {
  auto r = Parse(
      "class my_cls;\n"
      "  int data;\n"
      "  string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "my_cls");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[1]->name, "name");
}

// Class with end label.
TEST(SourceText, ClassEndLabel) {
  auto r = Parse("class C; endclass : C\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A2ClassDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  rand bit [7:0] payload;\n"
      "  function void display();\n"
      "    $display(\"pkt\");\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(Parser, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// A.1.9 Class items
// =============================================================================
// class_item ::= { attribute_instance } class_property (property_qualifier
// path)
TEST(SourceText, ClassPropertyWithQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  randc bit [3:0] y;\n"
      "  static int count;\n"
      "  protected int secret;\n"
      "  local int hidden;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand);
  EXPECT_EQ(members[0]->name, "x");
  EXPECT_TRUE(members[1]->is_randc);
  EXPECT_EQ(members[1]->name, "y");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_local);
}

// class_item_qualifier / property_qualifier / method_qualifier (footnote 10)
TEST(SourceText, ClassQualifierCombinations) {
  auto r = Parse(
      "class C;\n"
      "  static local int a;\n"
      "  protected rand int b;\n"
      "  static virtual function void sv_fn(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_TRUE(members[0]->is_static);
  EXPECT_TRUE(members[0]->is_local);
  EXPECT_TRUE(members[1]->is_protected);
  EXPECT_TRUE(members[1]->is_rand);
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[2]->is_virtual);
}

TEST(Parser, ClassWithMethod) {
  auto r = Parse(
      "class pkt;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_NE(cls->members[0]->method, nullptr);
}

// class_method ::= { method_qualifier } function_declaration
//                | { method_qualifier } task_declaration
TEST(SourceText, ClassMethods) {
  auto r = Parse(
      "class C;\n"
      "  function void foo(); endfunction\n"
      "  task bar(); endtask\n"
      "  static function int sfn(); endfunction\n"
      "  virtual task vtask(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "foo");
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->method->name, "bar");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_virtual);
}

// 13. Class with methods sharing scope with member variables
TEST(ParserClause03, Cl3_13_ClassMethodsAndProperties) {
  auto r = Parse(
      "class my_cls;\n"
      "  int count;\n"
      "  function void increment();\n"
      "    count = count + 1;\n"
      "  endfunction\n"
      "  task reset();\n"
      "    count = 0;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "count");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[1]->method, nullptr);
  EXPECT_EQ(cls->members[1]->method->name, "increment");
  EXPECT_EQ(cls->members[2]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[2]->method, nullptr);
  EXPECT_EQ(cls->members[2]->method->name, "reset");
}

// class_method ::= { method_qualifier } class_constructor_declaration
TEST(SourceText, ClassConstructorDecl) {
  auto r = Parse(
      "class C;\n"
      "  function new(int val);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ParserA24, ClassNewWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int a, int b);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyConstructorNew) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyConstructorNewEndLabel) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x);\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(Parser, ClassExtends) {
  auto r = Parse("class child extends parent; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "child");
  EXPECT_EQ(cls->base_class, "parent");
}

// Class with extends.
TEST(SourceText, ClassWithExtends) {
  auto r = Parse("class Child extends Parent; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Parent");
}

// =============================================================================
// A.1.2 class_declaration — additional forms
// =============================================================================
// Class with final_specifier: class :final C;
TEST(SourceText, ClassWithFinal) {
  auto r = Parse("class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// class_constructor_declaration with super.new()
TEST(SourceText, ClassConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
  EXPECT_EQ(r.cu->classes[1]->members[0]->method->name, "new");
}

TEST(Parser, ClassPropertyQualifiers) {
  auto r = Parse(
      "class pkt;\n"
      "  rand int data;\n"
      "  local int secret;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 2);
  EXPECT_TRUE(cls->members[0]->is_rand);
  EXPECT_TRUE(cls->members[1]->is_local);
}

// class_property ::= const { class_item_qualifier } data_type id [ = expr ] ;
TEST(SourceText, ClassConstProperty) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  const static int SMAX = 200;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_EQ(members[0]->name, "MAX");
  EXPECT_NE(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_TRUE(members[1]->is_static);
}

TEST(Parser, VirtualClass) {
  auto r = Parse("virtual class base; endclass");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// class_method ::= pure virtual { class_item_qualifier } method_prototype ;
//                | extern { method_qualifier } method_prototype ;
TEST(SourceText, ClassPureVirtualAndExtern) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function void pv_fn();\n"
      "  pure virtual task pv_task();\n"
      "  extern function void ext_fn();\n"
      "  extern static task ext_task();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_TRUE(members[1]->is_virtual);
  EXPECT_EQ(members[2]->method->name, "ext_fn");
  EXPECT_TRUE(members[3]->is_static);
}

TEST(ParserA26, FuncPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int compute(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task do_work(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 21. Class scope resolution (cls::member)
TEST(ParserClause03, Cl3_13_ClassScopeResolution) {
  EXPECT_TRUE(
      ParseOk("class base;\n"
              "  typedef int my_type;\n"
              "endclass\n"
              "module m;\n"
              "  base::my_type x;\n"
              "endmodule\n"));
}

// class_type (ps_class_identifier [param] { :: class_identifier [param] })
TEST(ParserA221, DataTypeClassType) {
  auto r = Parse(
      "class my_cls;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m; my_cls::my_type x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// method_prototype ::= task_prototype | function_prototype
TEST(SourceText, ClassMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function int get_val();\n"
      "  extern task do_work();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->method->name, "get_val");
  EXPECT_EQ(members[1]->method->name, "do_work");
}

// ---------------------------------------------------------------------------
// function_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// task_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA27, TaskBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern task my_task(input int x);\n"
      "endclass\n"
      "task C::my_task(input int x);\n"
      "  $display(\"x=%0d\", x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskBodyOutOfBlockMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Class with parameters.
TEST(SourceText, ClassWithParams) {
  auto r = Parse("class C #(type T = int); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// class_item ::= { attribute_instance } interface_class_declaration
TEST(SourceText, ClassNestedInterfaceClass) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class IFace;\n"
      "    pure virtual function void do_it();\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_TRUE(members[0]->nested_class->is_interface);
}

// interface_class_item ::= type_declaration | interface_class_method | params
TEST(SourceText, InterfaceClassItems) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void do_thing();\n"
      "  pure virtual task do_task();\n"
      "  typedef int my_int;\n"
      "  localparam int LP = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kTypedef);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kProperty);
}

// interface_class_declaration: interface class.
TEST(SourceText, InterfaceClassDecl) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
}

// =============================================================================
// §8 Class declarations — parsing
// =============================================================================
TEST(ParserSection8, EmptyClassDecl) {
  auto r = Parse("class Packet; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
}

TEST(ParserSection8, ClassWithProperties) {
  auto r = Parse(
      "class Packet;\n"
      "  int header;\n"
      "  int payload;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  const std::string kExpectedNames[] = {"header", "payload"};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(cls->members[i]->kind, ClassMemberKind::kProperty);
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

TEST(ParserSection8, ClassExtendsBase) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "Base");
  EXPECT_TRUE(r.cu->classes[0]->base_class.empty());
}

TEST(ParserSection8, ClassExtendsDerived) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->name, "Derived");
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ParserSection8, ClassWithQualifiersLocalProtected) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[0]->is_local);
  EXPECT_TRUE(cls->members[1]->is_protected);
}

TEST(ParserSection8, ClassWithQualifiersStaticRand) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[2]->is_static);
  EXPECT_TRUE(cls->members[3]->is_rand);
}

TEST(ParserSection8, ClassWithTask) {
  auto r = Parse(
      "class MyClass;\n"
      "  task do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->kind, ModuleItemKind::kTaskDecl);
}

TEST(ParserSection8, ClassWithConstraint) {
  auto r = Parse(
      "class Constrained;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint) {
      found = true;
      EXPECT_EQ(m->name, "c1");
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection8, ClassWithInitializer) {
  auto r = Parse(
      "class WithInit;\n"
      "  int x = 42;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_NE(cls->members[0]->init_expr, nullptr);
}

}  // namespace
