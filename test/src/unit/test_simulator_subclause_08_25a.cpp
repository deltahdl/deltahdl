#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/statement_assign_internal.h"

using namespace delta;

namespace {

// The value both a class parameter's default and an override of it are written
// as here: a bare identifier naming a variable. §6.8 makes that variable and
// the object's stored parameter two data storage elements, each storing "a
// value from one assignment to the next", so a store of the value the
// identifier produced has to take the words rather than the pointer to them --
// EvalExpr answers a bare identifier with the variable's own vector.
constexpr uint64_t kSeed = 0xDEADBEEFu;
constexpr uint64_t kSeedLowByteCleared = 0xDEADBE00u;

struct NamedVariable {
  Variable* var;
  Expr* expr;
};

NamedVariable MakeVariableAndItsName(SimFixture& f) {
  auto* var = f.ctx.CreateVariable("n", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, kSeed);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "n";
  return {var, expr};
}

// A class `P` with one #() value parameter `W`, whose default is `def` (null
// for a parameter declared without one, which is what an override supplies).
ClassTypeInfo* RegisterOneParamClass(SimFixture& f, Expr* def) {
  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "P";
  decl->params.push_back({"W", def});
  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "P";
  type->decl = decl;
  f.ctx.RegisterClassType("P", type);
  return type;
}

// Both keys the parameter is stored under: the bare name a use inside the
// class writes, and the "P::W" one a scoped access writes.
void ExpectStoredParameterOwnsItsWords(const Variable* var,
                                       const ClassObject* obj) {
  ASSERT_NE(obj, nullptr);
  ASSERT_NO_FATAL_FAILURE(
      ExpectOwnWordsCopy(var->value, obj->properties.at("W")));
  ASSERT_NO_FATAL_FAILURE(
      ExpectOwnWordsCopy(var->value, obj->properties.at("P::W")));
}

// The consequence of the sharing: DepositBitField writes through the words it
// finds rather than replacing them, so one buffer under the object and the
// variable carries a write to the stored parameter back to `n`.
void ExpectDepositLeavesTheNamedVariableIntact(SimFixture& f,
                                               const Variable* var,
                                               ClassObject* obj) {
  ASSERT_NE(obj, nullptr);
  DepositBitField(obj->properties["W"], 0, MakeLogic4VecVal(f.arena, 8, 0), 8);
  EXPECT_EQ(obj->properties["W"].ToUint64(), kSeedLowByteCleared);
  EXPECT_EQ(var->value.ToUint64(), kSeed);
}

// §8.25 gives a parameterized class's value parameter a default expression,
// which InitClassPropertyDefaults evaluates and stores when an object is
// constructed.
ClassObject* ConstructWithParamDefault(SimFixture& f, Expr* def) {
  RegisterOneParamClass(f, def);
  auto handle = EvalClassNew("P", nullptr, f.ctx, f.arena, {});
  return f.ctx.GetClassObject(handle.ToUint64());
}

// §8.25 overrides a parameter where the handle is declared -- `P #(.W(n)) c;`
// -- which the simulator records against the variable name and applies to the
// object the declaration constructed.
ClassObject* ConstructWithParamOverride(SimFixture& f, Expr* override_expr) {
  auto* type = RegisterOneParamClass(f, nullptr);
  auto* obj = f.arena.Create<ClassObject>();
  obj->type = type;
  auto handle = f.ctx.AllocateClassObject(obj);
  // The actuals as the parser records a declaration's `#(...)`: a value
  // actual is an implicit type carrying its expression.
  auto* actuals = f.arena.Create<std::vector<DataType>>();
  DataType actual;
  actual.type_ref_expr = override_expr;
  actuals->push_back(actual);
  RecordClassParamActuals("c", "P", *actuals, f.ctx);
  ApplyClassParamOverrides("c", handle, f.ctx, f.arena);
  return obj;
}

TEST(ClassSim, ClassParameterDefaultIsStoredOwningItsWords) {
  SimFixture f;
  auto [var, expr] = MakeVariableAndItsName(f);
  ASSERT_NO_FATAL_FAILURE(ExpectStoredParameterOwnsItsWords(
      var, ConstructWithParamDefault(f, expr)));
}

TEST(ClassSim, DepositIntoAParameterDefaultLeavesTheVariableIntact) {
  SimFixture f;
  auto [var, expr] = MakeVariableAndItsName(f);
  ASSERT_NO_FATAL_FAILURE(ExpectDepositLeavesTheNamedVariableIntact(
      f, var, ConstructWithParamDefault(f, expr)));
}

TEST(ClassSim, ClassParameterOverrideIsStoredOwningItsWords) {
  SimFixture f;
  auto [var, expr] = MakeVariableAndItsName(f);
  ASSERT_NO_FATAL_FAILURE(ExpectStoredParameterOwnsItsWords(
      var, ConstructWithParamOverride(f, expr)));
}

TEST(ClassSim, DepositIntoAParameterOverrideLeavesTheVariableIntact) {
  SimFixture f;
  auto [var, expr] = MakeVariableAndItsName(f);
  ASSERT_NO_FATAL_FAILURE(ExpectDepositLeavesTheNamedVariableIntact(
      f, var, ConstructWithParamOverride(f, expr)));
}

TEST(ClassSim, ParameterizedClassInstantiation) {
  SimFixture f;

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "Pair_int";
  type->properties.push_back({"first", 32, false});
  type->properties.push_back({"second", 32, false});
  f.ctx.RegisterClassType("Pair_int", type);

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("first", MakeLogic4VecVal(f.arena, 32, 10));
  obj->SetProperty("second", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("first", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("second", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, ParameterizedClassStaticMethod) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "Codec";
  decl->params.push_back({"W", nullptr});

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "Codec";
  type->decl = decl;

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "encode";
  method->is_static_method = true;
  type->methods["encode"] = method;

  f.ctx.RegisterClassType("Codec", type);

  auto* found = f.ctx.FindClassType("Codec");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("encode");
  ASSERT_NE(it, found->methods.end());
  EXPECT_TRUE(it->second->is_static_method);
}

TEST(ClassSim, SpecializationsHaveIndependentStaticMembers) {
  SimFixture f;

  auto* type_a = f.arena.Create<ClassTypeInfo>();
  type_a->name = "Vec_8";
  type_a->properties.push_back({"data", 8, false});
  type_a->properties.push_back({"count", 32, true});
  type_a->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_8", type_a);

  auto* type_b = f.arena.Create<ClassTypeInfo>();
  type_b->name = "Vec_16";
  type_b->properties.push_back({"data", 16, false});
  type_b->properties.push_back({"count", 32, true});
  type_b->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_16", type_b);

  type_a->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(type_a->static_properties["count"].ToUint64(), 42u);
  EXPECT_EQ(type_b->static_properties["count"].ToUint64(), 0u);
}

TEST(ClassSim, LoweredDefaultParamValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter int W = 16);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);

  auto it = info->static_properties.find("W");
  ASSERT_NE(it, info->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 16u);
}

TEST(ClassSim, LoweredMixedParams) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(type T = int, parameter int N = 4);\n"
      "    static function int get_n; get_n = N; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  ASSERT_NE(info->decl, nullptr);
  EXPECT_EQ(info->decl->params.size(), 2u);
  EXPECT_TRUE(info->decl->type_param_names.count("T"));
  EXPECT_FALSE(info->decl->type_param_names.count("N"));
}

// §8.25: a specialization is a generic class combined with a specific set of
// actual parameter values, and instances are declared with the same override
// rules as modules. Two distinct value-parameter specializations of the same
// generic class coexist and each object carries its own parameter value, read
// back here through the full pipeline via instance-qualified access.
TEST(ClassSim, ValueParameterDistinctPerSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] a;\n"
      "endclass\n"
      "module t;\n"
      "  int w8, w16;\n"
      "  initial begin\n"
      "    vector #(8) v8;\n"
      "    vector #(16) v16;\n"
      "    v8 = new;\n"
      "    v16 = new;\n"
      "    w8 = v8.width;\n"
      "    w16 = v16.width;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w8", 8u}, {"w16", 16u}});
}

// §8.25: all matching specializations of a generic class shall represent the
// same type. Two variables independently declared with the identical value-
// parameter specialization hold assignment-compatible handles: assigning one to
// the other aliases the same object, so a property written through the first is
// read back through the second. A mismatched type would make the handle
// assignment illegal.
TEST(ClassSim, MatchingSpecializationsAreSameType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(parameter width = 7);\n"
      "  int data;\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    vector #(4) a;\n"
      "    vector #(4) b;\n"
      "    a = new;\n"
      "    a.data = 55;\n"
      "    b = a;\n"
      "    r = b.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 55u}});
}

TEST(ClassSim, LoweredParamClassExtendsBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Base;\n"
      "    int x;\n"
      "  endclass\n"
      "  class Derived #(parameter int N = 4) extends Base;\n"
      "    int y;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("Derived");
  ASSERT_NE(info, nullptr);
  EXPECT_NE(info->parent, nullptr);
  EXPECT_EQ(info->parent->name, "Base");
  ASSERT_NE(info->decl, nullptr);
  EXPECT_EQ(info->decl->params.size(), 1u);
}

// §8.25: instances use the same override rules as modules, which include named
// parameter overrides. A named override supplies the value the instance reads
// back (the positional form is covered by
// ValueParameterDistinctPerSpecialization).
TEST(ClassSim, NamedParameterOverrideApplied) {
  EXPECT_EQ(RunAndGet("class vector #(parameter width = 7);\n"
                      "  int data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    vector #(.width(2)) v;\n"
                      "    v = new;\n"
                      "    out = v.width;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

// §8.25: a type parameter (here its default, int) determines the type of a
// class property, which is then usable at run time.
TEST(ClassSim, TypeParameterDefaultYieldsUsableProperty) {
  EXPECT_EQ(RunAndGet("class C #(type T = int);\n"
                      "  T data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.data = 42;\n"
                      "    out = c.data;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            42u);
}

// uvm_pool's shape: a property whose associative index (§7.8) is a type
// parameter of the class. §8.25 makes `pool #(string, int)` a specialization
// binding KEY to string, so the property is a string-keyed array and the
// entry add() writes is the one get() reads back through the class's own
// methods.
constexpr const char* kPoolClass =
    "class pool #(type KEY = int, type T = int);\n"
    "  protected T pool_[KEY];\n"
    "  function void add(KEY key, T item);\n"
    "    pool_[key] = item;\n"
    "  endfunction\n"
    "  function T get(KEY key);\n"
    "    if (pool_.exists(key)) return pool_[key];\n"
    "    return 0;\n"
    "  endfunction\n"
    "  function int has(KEY key);\n"
    "    return pool_.exists(key);\n"
    "  endfunction\n"
    "  function int count();\n"
    "    return pool_.num();\n"
    "  endfunction\n"
    "  function void drop(KEY key);\n"
    "    pool_.delete(key);\n"
    "  endfunction\n"
    "  function int total();\n"
    "    KEY k;\n"
    "    int sum = 0;\n"
    "    if (pool_.first(k))\n"
    "      do sum = sum + pool_[k];\n"
    "      while (pool_.next(k));\n"
    "    return sum;\n"
    "  endfunction\n"
    "endclass\n";

// Before the dimension naming a type parameter was read as one, IsAssocIndexDim
// saw no width for KEY and the property was no array at all: add() went
// nowhere and get() answered its 0.
TEST(ClassSim, TypeParameterIndexedPoolBoundToStringKeysAddsAndGets) {
  EXPECT_EQ(
      RunAndGet(std::string(kPoolClass) + "module t;\n"
                                          "  int out;\n"
                                          "  initial begin\n"
                                          "    pool #(string, int) p = new;\n"
                                          "    p.add(\"answer\", 42);\n"
                                          "    p.add(\"other\", 7);\n"
                                          "    out = p.get(\"answer\");\n"
                                          "  end\n"
                                          "endmodule\n",
                "out"),
      0x2Au);
}

// §7.9.3 and §7.9.1 through the same specialization: the key add() wrote
// exists, one it did not write does not, and num() counts the two entries.
TEST(ClassSim, TypeParameterIndexedPoolBoundToStringKeysReportsExistsAndNum) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    pool #(string, int) p = new;\n"
                          "    p.add(\"answer\", 42);\n"
                          "    p.add(\"other\", 7);\n"
                          "    out = p.has(\"answer\") * 100 +\n"
                          "          p.has(\"nope\") * 10 + p.count();\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            102u);
}

// §8.25.1: the unadorned name denotes the default specialization, KEY its
// default int, so the property is an int-keyed array.
TEST(ClassSim, TypeParameterIndexedPoolDefaultsToIntKeys) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) + "module t;\n"
                                                "  int out;\n"
                                                "  initial begin\n"
                                                "    pool p;\n"
                                                "    p = new;\n"
                                                "    p.add(5, 42);\n"
                                                "    p.add(9, 1);\n"
                                                "    out = p.get(5);\n"
                                                "  end\n"
                                                "endmodule\n",
                      "out"),
            0x2Au);
}

TEST(ClassSim, TypeParameterIndexedPoolDefaultKeysReportExistsAndNum) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    pool p = new;\n"
                          "    p.add(5, 42);\n"
                          "    p.add(9, 1);\n"
                          "    out = p.has(5) * 100 + p.has(6) * 10 +\n"
                          "          p.count();\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            102u);
}

// §7.9.2 and §7.9.4 through §7.9.6 on the default specialization: delete()
// removes the one entry, and first()/next() over a local of the KEY type
// visit the two that remain.
TEST(ClassSim, TypeParameterIndexedPoolDeletesAndTraverses) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    pool p = new;\n"
                          "    p.add(1, 10);\n"
                          "    p.add(2, 20);\n"
                          "    p.add(3, 30);\n"
                          "    p.drop(2);\n"
                          "    out = p.total() * 10 + p.count();\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            402u);
}

// §8.25 with §7.10: a queue property whose element type is a type parameter,
// `T items[$]`, is a queue of the object in every specialization: the default
// `stack` pops the 7 it pushed, and `stack #(bit [3:0])` pops the 4 pushed
// last of two and then counts one element.
TEST(ClassSim, TypeParameterQueuePropertyInEachSpecialization) {
  EXPECT_EQ(RunAndGet("class stack #(type T = int);\n"
                      "  local T items[$];\n"
                      "  function void push(T a);\n"
                      "    items.push_back(a);\n"
                      "  endfunction\n"
                      "  function T pop();\n"
                      "    return items.pop_back();\n"
                      "  endfunction\n"
                      "  function int n();\n"
                      "    return items.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    stack is = new;\n"
                      "    stack #(bit [3:0]) bs = new;\n"
                      "    is.push(7);\n"
                      "    bs.push(4'd12);\n"
                      "    bs.push(4'd4);\n"
                      "    out = is.pop() * 100 + bs.pop() * 10 + bs.n();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            741u);
}

// §8.25 (printed page 203 of IEEE 1800-2023) instantiates an object under
// the parameter override rules of §23.10, whose §23.10.2.2 binds an actual
// written `.name(value)` to the parameter of that name whatever its
// position. The value actuals were bound by position alone, so `#(.E(7))`
// on a class whose first parameter is D wrote 7 into D and left E at its
// default: mul() gave 7 * 1 rather than 3 * 7.
TEST(ClassSim, NamedValueActualBindsTheParameterOfItsName) {
  EXPECT_EQ(RunAndGet("class G #(int D = 3, int E = 1);\n"
                      "  function int mul();\n"
                      "    return D * E;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    G #(.E(7)) b;\n"
                      "    b = new;\n"
                      "    out = b.mul();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            21u);
}

// §8.25 (printed page 203 of IEEE 1800-2023): an object is instantiated
// with the parameter override rules of §23.10, `vector #(10) vten;`, and inside
// its methods a value parameter names what the specialization bound it to.
// Declared at module scope, `G #(5) b = new;` constructed the class's default
// specialization: the lowerer built the object without recording the
// declaration's parameter value assignment, which only a declaration inside a
// procedural block recorded, so a method of `b` read D as 3, whether as the
// value or as the delay `#D`. The task reads D as a delay and as a value, so
// the time and the value are both bound: a default-specialized object gives
// 3 and 3 @ 3, the `#(5)` object 5 @ 8, packed as 5 * 100 + 8.
TEST(ClassSim, ValueParameterOfAModuleScopeSpecializationReadInAMethod) {
  EXPECT_EQ(RunAndGet("class G #(int D = 3);\n"
                      "  int seen;\n"
                      "  task run;\n"
                      "    #D seen = D * 100 + $time;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  G #() a = new;\n"
                      "  G #(5) b = new;\n"
                      "  initial begin\n"
                      "    a.run();\n"
                      "    b.run();\n"
                      "    out = a.seen * 10000 + b.seen;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            303u * 10000u + 508u);
}

// §8.25 with §23.10: the same at module scope where the handle is declared
// with the specialization and constructed later in a procedural block,
// `G #(5) b;` then `b = new;`, and the parameter is bound by name.
TEST(ClassSim, ValueParameterOfAModuleScopeSpecializationConstructedLater) {
  EXPECT_EQ(RunAndGet("class G #(int D = 3, int E = 1);\n"
                      "  function int mul();\n"
                      "    return D * E;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  G #(.E(7)) b;\n"
                      "  initial begin\n"
                      "    b = new;\n"
                      "    out = b.mul();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            21u);
}

// §8.25's own generic class, `class vector #(int size = 1); bit [size-1:0]
// a;` (printed page 203 of IEEE 1800-2023), sizes a property by the
// class's value parameter, which §6.20.1 declares in the class's parameter port
// list or its body (printed 125). The lowerer sized every property with no
// parameter in scope, so `logic [W-1:0] v` was one bit wide: `c.v = '1`
// stored 1 and `$bits(c.v)` answered 1. Here v is sized by the header
// parameter and u by a body localparam derived from it, so the write of all
// ones reads 255 and the widths 8 and 16: 255 + 16 * 1000 + 8 * 100000.
TEST(ClassSim, PropertyWidthNamesTheClassParameters) {
  EXPECT_EQ(
      RunAndGet("class C #(int W = 8);\n"
                "  localparam int N = W * 2;\n"
                "  logic [W-1:0] v;\n"
                "  logic [N-1:0] u;\n"
                "endclass\n"
                "module t;\n"
                "  int out;\n"
                "  initial begin\n"
                "    C c;\n"
                "    c = new;\n"
                "    c.v = '1;\n"
                "    out = c.v + $bits(c.u) * 1000 + $bits(c.v) * 100000;\n"
                "  end\n"
                "endmodule\n",
                "out"),
      255u + 16u * 1000u + 8u * 100000u);
}

// §8.25: a specialization `stack #(bit [2:0])` binds the type parameter T to
// `bit [2:0]` throughout the class body (printed pages 203-204 of IEEE
// 1800-2023), so §20.6.2's `$bits(T)` in an instance method is 3, and the
// object of the default specialization (§8.25.1) reads the default int's 32.
// EvalBits asked the type table alone, which holds the class's default for the
// name, so the specialized object read 32 too. The three objects are declared
// at module scope, in a procedural block and with the actual bound by name.
TEST(ClassSim, BitsOfATypeParameterReadsTheSpecializationsActual) {
  EXPECT_EQ(RunAndGet("class stack #(type T = int);\n"
                      "  function int bits();\n"
                      "    return $bits(T);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  stack #(bit [2:0]) s3 = new;\n"
                      "  stack s0 = new;\n"
                      "  initial begin\n"
                      "    stack #(.T(logic [6:0])) s7 = new;\n"
                      "    out = s3.bits() * 10000 + s7.bits() * 100 +\n"
                      "          s0.bits();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3u * 10000u + 7u * 100u + 32u);
}

// §8.25 with §7.8: `table_c #(string, int)` declared at module scope makes
// `V m[K]` a string-keyed associative array of int, so two puts give num() 2
// and get("b") 31, and the int-keyed `table_c #(int, int)` gets 42 back for
// key 5 -- 2 * 10000 + 31 * 100 + 42.
TEST(ClassSim, TypeParameterIndexedPropertyOfAModuleScopeSpecialization) {
  EXPECT_EQ(RunAndGet("class table_c #(type K = int, type V = int);\n"
                      "  V m[K];\n"
                      "  function void put(K k, V v); m[k] = v; endfunction\n"
                      "  function V get(K k); return m[k]; endfunction\n"
                      "  function int size(); return m.num(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  table_c #(string, int) ts = new;\n"
                      "  table_c #(int, int) ti = new;\n"
                      "  initial begin\n"
                      "    ts.put(\"a\", 30); ts.put(\"b\", 31);\n"
                      "    ti.put(5, 42);\n"
                      "    out = ts.size() * 10000 + ts.get(\"b\") * 100 +\n"
                      "          ti.get(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u * 10000u + 31u * 100u + 42u);
}

// §8.25's own chain (printed page 204 of IEEE 1800-2023): a class
// extending a parameterized class binds the base's type parameter as its
// extends clause says -- `extends C` takes C's default bit, `extends C
// #(integer)` binds integer, and `extends C #(P)` binds the derived class's own
// type parameter, real by default -- so the inherited `T x` is 1, 32 and 64
// bits wide through the base's `$bits(x)`. The base's properties were sized by
// the base's defaults alone, 32 in every case (bit fell to the 32-bit carrier),
// so d1 read 32 and d3 32 -- 1 * 100000 + 32 * 1000 + 64.
TEST(ClassSim, BaseTypeParameterBoundThroughExtendsSizesTheProperty) {
  EXPECT_EQ(RunAndGet("class C #(type T = bit);\n"
                      "  T x;\n"
                      "  function int w(); return $bits(x); endfunction\n"
                      "endclass\n"
                      "class D1 #(type P = real) extends C; endclass\n"
                      "class D2 #(type P = real) extends C #(integer);\n"
                      "endclass\n"
                      "class D3 #(type P = real) extends C #(P); endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  D1 d1 = new; D2 d2 = new; D3 d3 = new;\n"
                      "  initial out = d1.w() * 100000 + d2.w() * 1000 +\n"
                      "                d3.w();\n"
                      "endmodule\n",
                      "out"),
            1u * 100000u + 32u * 1000u + 64u);
}

// The binding reaches down two levels: E extends D3 #(bit [15:0]), whose P is
// C's T, so E's inherited x is 16 bits; and a value written into the bound
// property keeps the bound width, `x = 16'hFFFF` reading 65535 through the
// base's method where a 1-bit x would read 1 -- 16 * 100000 + 65535.
TEST(ClassSim, BaseTypeParameterBoundThroughTwoExtendsLevels) {
  EXPECT_EQ(RunAndGet("class C #(type T = bit);\n"
                      "  T x;\n"
                      "  function int w(); return $bits(x); endfunction\n"
                      "  function int rd(); return x; endfunction\n"
                      "endclass\n"
                      "class D3 #(type P = real) extends C #(P); endclass\n"
                      "class E extends D3 #(bit [15:0]); endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  E e = new;\n"
                      "  initial begin\n"
                      "    e.x = 16'hFFFF;\n"
                      "    out = e.w() * 100000 + e.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            16u * 100000u + 65535u);
}

// §8.25's D4 (printed page 205 of IEEE 1800-2023): the base class may be
// named by a type parameter of the derived class, `class D4 #(type P =
// C#(byte)) extends P;` extending the class the parameter's default names with
// the default's own actuals, so the default specialization of D4 inherits C's
// members with T bound to byte and the inherited `T x` is 8 bits wide
// through the base's `$bits(x)`. The lowerer looked the base up under the
// parameter's name, found no class, and D4 inherited nothing, so `d4.w()`
// ran no method and read 0; C's default bit would read 1 and an unbound T
// the 32-bit carrier.
TEST(ClassSim, BaseNamedByATypeParameterExtendsTheDefaultsClass) {
  EXPECT_EQ(RunAndGet("class C #(type T = bit);\n"
                      "  T x;\n"
                      "  function int w(); return $bits(x); endfunction\n"
                      "endclass\n"
                      "class D4 #(type P = C#(byte)) extends P; endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  D4 d4 = new;\n"
                      "  initial out = d4.w();\n"
                      "endmodule\n",
                      "out"),
            8u);
}

// The parameter naming the base is bound through an extends clause of a
// level below: E extends D4 #(C#(shortint)), so on an E object D4's P is
// C#(shortint) and C's T is shortint, the inherited x 16 bits wide rather
// than the default's 8, and a value written into it keeps the bound width,
// `x = 16'hFFFF` reading 65535 through the base's method where an 8-bit x
// would read 255 -- 16 * 100000 + 65535.
TEST(ClassSim, BaseNamedByATypeParameterBoundThroughAnExtendsLevel) {
  EXPECT_EQ(RunAndGet("class C #(type T = bit);\n"
                      "  T x;\n"
                      "  function int w(); return $bits(x); endfunction\n"
                      "  function int rd(); return x; endfunction\n"
                      "endclass\n"
                      "class D4 #(type P = C#(byte)) extends P; endclass\n"
                      "class E extends D4 #(C#(shortint)); endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  E e = new;\n"
                      "  initial begin\n"
                      "    e.x = 16'hFFFF;\n"
                      "    out = e.w() * 100000 + e.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            16u * 100000u + 65535u);
}

// §8.25 (printed page 204 of IEEE 1800-2023): a type parameter may be
// bound to a class type, so a property declared with the parameter as its type,
// `T obj` in `class Holder #(type T = Item)`, is a handle of the bound class --
// of Item in the default specialization (§8.25.1) -- and `obj = new` in the
// constructor builds an Item whose `get()` answers its `v`, 12. The `new`
// was resolved against a class named T, which there is none of, so nothing
// was built and `obj.get()` through the null handle read 0.
TEST(ClassSim, TypeParameterClassPropertyBuiltInTheConstructor) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v = 12;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class Holder #(type T = Item);\n"
                      "  T obj;\n"
                      "  function new(); obj = new; endfunction\n"
                      "  function int read(); return obj.get(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Holder h = new;\n"
                      "  int r;\n"
                      "  initial r = h.read();\n"
                      "endmodule\n",
                      "r"),
            12u);
}

// The same property on a `Holder #(Item2)` object is a handle of Item2, whose
// `get()` overrides Item's to answer 99: the class built is the one the
// specialization binds T to, where one fixed to the default would build an
// Item and read 12. The object is built by a method run after the
// declaration has bound the actual to the object; #4344 covers binding it
// before the constructor runs.
TEST(ClassSim, TypeParameterClassPropertyBuiltAsTheBoundClass) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v = 12;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class Item2 extends Item;\n"
                      "  function int get(); return 99; endfunction\n"
                      "endclass\n"
                      "class Holder #(type T = Item);\n"
                      "  T obj;\n"
                      "  function void build(); obj = new; endfunction\n"
                      "  function int read(); return obj.get(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Holder #(Item2) h2 = new;\n"
                      "  int r2;\n"
                      "  initial begin\n"
                      "    h2.build();\n"
                      "    r2 = h2.read();\n"
                      "  end\n"
                      "endmodule\n",
                      "r2"),
            99u);
}

// A property of the bound class is read through the handle directly, `obj.v`,
// beside the method: Item2's constructor sets v to 34, so the bound Item2
// reads 34 * 100 + 99 where an Item would read 12 * 100 + 12 and a null
// handle 0.
TEST(ClassSim, TypeParameterClassPropertyReadThroughItsHandle) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v = 12;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class Item2 extends Item;\n"
                      "  function new(); v = 34; endfunction\n"
                      "  function int get(); return 99; endfunction\n"
                      "endclass\n"
                      "class Holder #(type T = Item);\n"
                      "  T obj;\n"
                      "  function void build(); obj = new; endfunction\n"
                      "  function int read();\n"
                      "    return obj.v * 100 + obj.get();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Holder #(Item2) h2 = new;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    h2.build();\n"
                      "    r = h2.read();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            34u * 100u + 99u);
}

// §8.7 with §8.25: the `new` may stand as the property's initializer, `T obj
// = new;`, which InitClassPropertyDefault resolves through the same class:
// the default specialization builds an Item and reads 12.
TEST(ClassSim, TypeParameterClassPropertyNewInitializer) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v = 12;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class Holder #(type T = Item);\n"
                      "  T obj = new;\n"
                      "  function int read(); return obj.get(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Holder h = new;\n"
                      "  int r;\n"
                      "  initial r = h.read();\n"
                      "endmodule\n",
                      "r"),
            12u);
}

// And through a handle from outside the class, `h2.obj = new`, where the
// class is read off the object the handle refers to: bound to Item2, the
// object built answers 99.
TEST(ClassSim, TypeParameterClassPropertyBuiltThroughAHandle) {
  EXPECT_EQ(RunAndGet("class Item;\n"
                      "  int v = 12;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class Item2 extends Item;\n"
                      "  function int get(); return 99; endfunction\n"
                      "endclass\n"
                      "class Holder #(type T = Item);\n"
                      "  T obj;\n"
                      "  function int read(); return obj.get(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  Holder #(Item2) h2 = new;\n"
                      "  int r2;\n"
                      "  initial begin\n"
                      "    h2.obj = new;\n"
                      "    r2 = h2.read();\n"
                      "  end\n"
                      "endmodule\n",
                      "r2"),
            99u);
}

}  // namespace
