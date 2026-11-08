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

void ExpectStoredParameterOwnsItsWords(const Variable* var,
                                       const ClassObject* obj) {
  ASSERT_NE(obj, nullptr);
  ASSERT_NO_FATAL_FAILURE(
      ExpectOwnWordsCopy(var->value, obj->properties.at("W")));
  ASSERT_NO_FATAL_FAILURE(
      ExpectOwnWordsCopy(var->value, obj->properties.at("P::W")));
}

void ExpectDepositLeavesTheNamedVariableIntact(SimFixture& f,
                                               const Variable* var,
                                               ClassObject* obj) {
  ASSERT_NE(obj, nullptr);
  DepositBitField(obj->properties["W"], 0, MakeLogic4VecVal(f.arena, 8, 0), 8);
  EXPECT_EQ(obj->properties["W"].ToUint64(), kSeedLowByteCleared);
  EXPECT_EQ(var->value.ToUint64(), kSeed);
}

ClassObject* ConstructWithParamDefault(SimFixture& f, Expr* def) {
  RegisterOneParamClass(f, def);
  auto handle = EvalClassNew("P", nullptr, f.ctx, f.arena, {});
  return f.ctx.GetClassObject(handle.ToUint64());
}

ClassObject* ConstructWithParamOverride(SimFixture& f, Expr* override_expr) {
  auto* type = RegisterOneParamClass(f, nullptr);
  auto* obj = f.arena.Create<ClassObject>();
  obj->type = type;
  auto handle = f.ctx.AllocateClassObject(obj);
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

TEST(ClassSim, TypeParameterIndexedPoolBoundToStringKeysAddsAndGets) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    static pool #(string, int) p = new;\n"
                          "    p.add(\"answer\", 42);\n"
                          "    p.add(\"other\", 7);\n"
                          "    out = p.get(\"answer\");\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            0x2Au);
}

TEST(ClassSim, TypeParameterIndexedPoolBoundToStringKeysReportsExistsAndNum) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    static pool #(string, int) p = new;\n"
                          "    p.add(\"answer\", 42);\n"
                          "    p.add(\"other\", 7);\n"
                          "    out = p.has(\"answer\") * 100 +\n"
                          "          p.has(\"nope\") * 10 + p.count();\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            102u);
}

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
                          "    static pool p = new;\n"
                          "    p.add(5, 42);\n"
                          "    p.add(9, 1);\n"
                          "    out = p.has(5) * 100 + p.has(6) * 10 +\n"
                          "          p.count();\n"
                          "  end\n"
                          "endmodule\n",
                      "out"),
            102u);
}

TEST(ClassSim, TypeParameterIndexedPoolDeletesAndTraverses) {
  EXPECT_EQ(RunAndGet(std::string(kPoolClass) +
                          "module t;\n"
                          "  int out;\n"
                          "  initial begin\n"
                          "    static pool p = new;\n"
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
                      "    static stack is = new;\n"
                      "    static stack #(bit [3:0]) bs = new;\n"
                      "    is.push(7);\n"
                      "    bs.push(4'd12);\n"
                      "    bs.push(4'd4);\n"
                      "    out = is.pop() * 100 + bs.pop() * 10 + bs.n();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            741u);
}

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
                      "    static stack #(.T(logic [6:0])) s7 = new;\n"
                      "    out = s3.bits() * 10000 + s7.bits() * 100 +\n"
                      "          s0.bits();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3u * 10000u + 7u * 100u + 32u);
}

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
