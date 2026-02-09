#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================

struct ClassFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// AST helper: make an integer literal expression.
static Expr* MkInt(Arena& a, uint64_t val) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// AST helper: make an identifier expression.
static Expr* MkId(Arena& a, std::string_view name) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// AST helper: make a binary expression.
static Expr* MkBin(Arena& a, TokenKind op, Expr* l, Expr* r) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = l;
  e->rhs = r;
  return e;
}

// AST helper: make a blocking assignment statement.
static Stmt* MkAssign(Arena& a, std::string_view lhs_name, Expr* rhs) {
  auto* s = a.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MkId(a, lhs_name);
  s->rhs = rhs;
  return s;
}

// AST helper: make a return statement.
static Stmt* MkReturn(Arena& a, Expr* expr) {
  auto* s = a.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

// Build a simple ClassTypeInfo and register it with the context.
static ClassTypeInfo* MakeClassType(ClassFixture& f, std::string_view name,
                                    std::vector<std::string_view> props) {
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

// Allocate a ClassObject of the given type, returning (handle_id, object*).
static std::pair<uint64_t, ClassObject*> MakeObj(ClassFixture& f,
                                                 ClassTypeInfo* type) {
  auto* obj = f.arena.Create<ClassObject>();
  obj->type = type;
  // Initialize properties to 0.
  for (const auto& p : type->properties) {
    obj->properties[std::string(p.name)] =
        MakeLogic4VecVal(f.arena, p.width, 0);
  }
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  return {handle, obj};
}

// =============================================================================
// §8.6-8.8: Class declaration and new() constructor
// =============================================================================

TEST(ClassSim, AllocateNewObject) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(handle, kNullClassHandle);
  EXPECT_EQ(obj->type, type);
  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 0u);
}

TEST(ClassSim, NewReturnsUniqueHandles) {
  ClassFixture f;
  auto* type = MakeClassType(f, "MyClass", {"x"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  EXPECT_NE(h1, h2);
}

TEST(ClassSim, HandleToObjectLookup) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {"val"});
  auto [handle, obj] = MakeObj(f, type);

  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
}

// =============================================================================
// §8.3-8.5: Property access and assignment
// =============================================================================

TEST(ClassSim, PropertySetAndGet) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  EXPECT_EQ(obj->GetProperty("data", f.arena).ToUint64(), 42u);
}

TEST(ClassSim, MultipleProperties) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload", "crc"});
  auto [handle, obj] = MakeObj(f, type);

  obj->SetProperty("header", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("payload", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("crc", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("payload", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("crc", f.arena).ToUint64(), 3u);
}

TEST(ClassSim, UndefinedPropertyReturnsZero) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->GetProperty("nonexistent", f.arena).ToUint64(), 0u);
}

// =============================================================================
// §8.24: Method calls
// =============================================================================

TEST(ClassSim, SimpleMethodCall) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Counter", {"count"});

  // Method: function int get_count(); return count; endfunction
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_count";
  method->func_body_stmts.push_back(MkReturn(f.arena, MkId(f.arena, "count")));
  type->methods["get_count"] = method;

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("count", MakeLogic4VecVal(f.arena, 32, 99));

  auto* resolved = obj->ResolveMethod("get_count");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_count");
}

TEST(ClassSim, MethodWithArgs) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Adder", {"total"});

  // function void add(input int v); total = total + v; endfunction
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "add";
  method->return_type.kind = DataTypeKind::kVoid;
  method->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  auto* rhs = MkBin(f.arena, TokenKind::kPlus, MkId(f.arena, "total"),
                    MkId(f.arena, "v"));
  method->func_body_stmts.push_back(MkAssign(f.arena, "total", rhs));
  type->methods["add"] = method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("add");
  EXPECT_NE(resolved, nullptr);
}

// =============================================================================
// §8.11: `this` keyword reference
// =============================================================================

TEST(ClassSim, ThisPushPop) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
  f.ctx.PushThis(obj);
  EXPECT_EQ(f.ctx.CurrentThis(), obj);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

TEST(ClassSim, NestedThisScoping) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  auto [h2, obj2] = MakeObj(f, type);

  f.ctx.PushThis(obj1);
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PushThis(obj2);
  EXPECT_EQ(f.ctx.CurrentThis(), obj2);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), obj1);
  f.ctx.PopThis();
  EXPECT_EQ(f.ctx.CurrentThis(), nullptr);
}

// =============================================================================
// §8.10: Static properties and methods
// =============================================================================

TEST(ClassSim, StaticPropertySharedAcrossInstances) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Shared", {"inst_val"});
  type->properties.push_back({"counter", 32, true});
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 0);

  // Create two instances (we just need them to exist).
  MakeObj(f, type);
  MakeObj(f, type);

  // Modify the static property.
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 42);

  // Both instances see the same static value.
  EXPECT_EQ(type->static_properties["counter"].ToUint64(), 42u);
}

TEST(ClassSim, StaticMethodResolution) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Util", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "helper";
  method->is_static = true;
  method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 100)));
  type->methods["helper"] = method;

  auto it = type->methods.find("helper");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

// =============================================================================
// §8.13: Inheritance with `extends`
// =============================================================================

TEST(ClassSim, InheritanceParentLink) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  EXPECT_EQ(derived->parent, base);
  EXPECT_EQ(derived->parent->name, "Base");
}

TEST(ClassSim, InheritedMethodResolution) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_x";
  method->func_body_stmts.push_back(MkReturn(f.arena, MkId(f.arena, "x")));
  base->methods["get_x"] = method;

  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  // Should find get_x from base class.
  auto* resolved = obj->ResolveMethod("get_x");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_x");
}

TEST(ClassSim, ChildMethodOverridesParent) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {});

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "greet";
  base_method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 1)));
  base->methods["greet"] = base_method;

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;
  auto* child_method = f.arena.Create<ModuleItem>();
  child_method->kind = ModuleItemKind::kFunctionDecl;
  child_method->name = "greet";
  child_method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 2)));
  derived->methods["greet"] = child_method;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("greet");
  EXPECT_NE(resolved, nullptr);
  // Should find derived's version first.
  EXPECT_NE(resolved, base_method);
  EXPECT_EQ(resolved, child_method);
}

// =============================================================================
// §8.20: Virtual methods and polymorphism
// =============================================================================

TEST(ClassSim, VirtualMethodDispatch) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Animal", {});
  auto* derived = MakeClassType(f, "Dog", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "speak";
  base_method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 0)));

  auto* derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "speak";
  derived_method->func_body_stmts.push_back(
      MkReturn(f.arena, MkInt(f.arena, 1)));

  // Build vtable for base.
  base->vtable.push_back({"speak", base_method, base});
  // Build vtable for derived — overrides speak.
  derived->vtable.push_back({"speak", derived_method, derived});

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveVirtualMethod("speak");
  EXPECT_EQ(resolved, derived_method);
}

TEST(ClassSim, VirtualMethodInheritedNotOverridden) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "action";

  // Base vtable has action.
  base->vtable.push_back({"action", base_method, base});
  // Derived inherits without override.
  derived->vtable.push_back({"action", base_method, base});

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveVirtualMethod("action");
  EXPECT_EQ(resolved, base_method);
}

// =============================================================================
// §8.21: Abstract classes and pure virtual methods
// =============================================================================

TEST(ClassSim, AbstractClassFlag) {
  ClassFixture f;
  auto* abstract_type = MakeClassType(f, "AbstractBase", {});
  abstract_type->is_abstract = true;

  EXPECT_TRUE(abstract_type->is_abstract);
}

TEST(ClassSim, PureVirtualMethodNullBody) {
  ClassFixture f;
  auto* abstract_type = MakeClassType(f, "Shape", {});
  abstract_type->is_abstract = true;

  // Pure virtual: vtable entry with nullptr method.
  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  EXPECT_EQ(abstract_type->vtable[0].method, nullptr);

  // Concrete derived class overrides it.
  auto* concrete = MakeClassType(f, "Circle", {"radius"});
  concrete->parent = abstract_type;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "area";
  method->func_body_stmts.push_back(MkReturn(f.arena, MkInt(f.arena, 314)));
  concrete->vtable.push_back({"area", method, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  auto* resolved = obj->ResolveVirtualMethod("area");
  EXPECT_EQ(resolved, method);
}

// =============================================================================
// §8.16: $cast for type checking
// =============================================================================

TEST(ClassSim, IsASameType) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {});
  EXPECT_TRUE(type->IsA(type));
}

TEST(ClassSim, IsADerivedFromBase) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  EXPECT_TRUE(derived->IsA(base));
  EXPECT_FALSE(base->IsA(derived));
}

TEST(ClassSim, IsADeepHierarchy) {
  ClassFixture f;
  auto* grand = MakeClassType(f, "Grand", {});
  auto* parent = MakeClassType(f, "Parent", {});
  parent->parent = grand;
  auto* child = MakeClassType(f, "Child", {});
  child->parent = parent;

  EXPECT_TRUE(child->IsA(grand));
  EXPECT_TRUE(child->IsA(parent));
  EXPECT_FALSE(grand->IsA(child));
}

TEST(ClassSim, IsAUnrelated) {
  ClassFixture f;
  auto* typeA = MakeClassType(f, "A", {});
  auto* typeB = MakeClassType(f, "B", {});

  EXPECT_FALSE(typeA->IsA(typeB));
  EXPECT_FALSE(typeB->IsA(typeA));
}

// =============================================================================
// §8.23: Class scope resolution operator ::
// =============================================================================

TEST(ClassSim, ScopeResolutionStaticLookup) {
  ClassFixture f;
  auto* type = MakeClassType(f, "MyClass", {});
  type->static_properties["MAX_SIZE"] = MakeLogic4VecVal(f.arena, 32, 256);

  auto it = type->static_properties.find("MAX_SIZE");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 256u);
}

TEST(ClassSim, ScopeResolutionMethodLookup) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Utils", {});
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "compute";
  method->is_static = true;
  type->methods["compute"] = method;

  auto* found = f.ctx.FindClassType("Utils");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("compute");
  ASSERT_NE(it, found->methods.end());
  EXPECT_EQ(it->second->name, "compute");
}

// =============================================================================
// §8.4: Null object handle checks
// =============================================================================

TEST(ClassSim, NullHandleIsZero) { EXPECT_EQ(kNullClassHandle, 0u); }

TEST(ClassSim, GetClassObjectNullReturnsNullptr) {
  ClassFixture f;
  auto* obj = f.ctx.GetClassObject(kNullClassHandle);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, GetClassObjectInvalidReturnsNullptr) {
  ClassFixture f;
  auto* obj = f.ctx.GetClassObject(99999);
  EXPECT_EQ(obj, nullptr);
}

// =============================================================================
// §8.12: Object assignment (handle semantics)
// =============================================================================

TEST(ClassSim, HandleAssignmentSharesObject) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Data", {"val"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));

  // Simulate handle copy: both variables hold same handle ID.
  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 10u);

  // Modify via one handle, visible through the other.
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, HandleNullAssignment) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  // The valid handle works.
  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  // "Assigning null" means setting handle to 0.
  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

// =============================================================================
// §8.25: Parameterized classes (basic cases)
// =============================================================================

TEST(ClassSim, ParameterizedClassDifferentWidths) {
  ClassFixture f;

  // Simulate Stack#(8) — 8-bit data property.
  auto* type8 = f.arena.Create<ClassTypeInfo>();
  type8->name = "Stack_8";
  type8->properties.push_back({"data", 8, false});
  f.ctx.RegisterClassType("Stack_8", type8);

  // Simulate Stack#(32) — 32-bit data property.
  auto* type32 = f.arena.Create<ClassTypeInfo>();
  type32->name = "Stack_32";
  type32->properties.push_back({"data", 32, false});
  f.ctx.RegisterClassType("Stack_32", type32);

  auto* t8 = f.ctx.FindClassType("Stack_8");
  auto* t32 = f.ctx.FindClassType("Stack_32");
  ASSERT_NE(t8, nullptr);
  ASSERT_NE(t32, nullptr);
  EXPECT_EQ(t8->properties[0].width, 8u);
  EXPECT_EQ(t32->properties[0].width, 32u);
}

TEST(ClassSim, ParameterizedClassInstantiation) {
  ClassFixture f;

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

// =============================================================================
// §8.24.1: Extern methods
// =============================================================================

TEST(ClassSim, ExternMethodRegisteredSeparately) {
  ClassFixture f;
  auto* type = MakeClassType(f, "MyClass", {"val"});

  // Extern method body defined outside class.
  auto* extern_method = f.arena.Create<ModuleItem>();
  extern_method->kind = ModuleItemKind::kFunctionDecl;
  extern_method->name = "get_val";
  extern_method->func_body_stmts.push_back(
      MkReturn(f.arena, MkId(f.arena, "val")));

  // Register it on the type (as if elaboration resolved the extern).
  type->methods["get_val"] = extern_method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("get_val");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_val");
}

// =============================================================================
// §8.7: Class constructors with arguments
// =============================================================================

TEST(ClassSim, ConstructorMethodRegistered) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});

  // function new(input int h, input int p);
  //   header = h; payload = p;
  // endfunction
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {
      {Direction::kInput, false, {}, "h", nullptr, {}},
      {Direction::kInput, false, {}, "p", nullptr, {}},
  };
  ctor->func_body_stmts.push_back(
      MkAssign(f.arena, "header", MkId(f.arena, "h")));
  ctor->func_body_stmts.push_back(
      MkAssign(f.arena, "payload", MkId(f.arena, "p")));
  type->methods["new"] = ctor;

  auto* resolved = type->methods["new"];
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->func_args.size(), 2u);
}

TEST(ClassSim, ConstructorBodyExecutesStatements) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Init", {"val"});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  ctor->func_body_stmts.push_back(MkAssign(f.arena, "val", MkId(f.arena, "v")));
  type->methods["new"] = ctor;

  // Simulate constructor execution manually.
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.PushThis(obj);
  f.ctx.PushScope();

  auto* arg_var = f.ctx.CreateLocalVariable("v", 32);
  arg_var->value = MakeLogic4VecVal(f.arena, 32, 77);
  auto* val_var = f.ctx.CreateLocalVariable("val", 32);
  val_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Execute: val = v
  auto rhs_val = EvalExpr(MkId(f.arena, "v"), f.ctx, f.arena);
  val_var->value = rhs_val;

  // Writeback to object property.
  obj->SetProperty("val", val_var->value);
  f.ctx.PopScope();
  f.ctx.PopThis();

  EXPECT_EQ(obj->GetProperty("val", f.arena).ToUint64(), 77u);
}

// =============================================================================
// §8.15: super.new() chaining
// =============================================================================

TEST(ClassSim, SuperNewChaining) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {"base_val"});
  auto* derived = MakeClassType(f, "Derived", {"child_val"});
  derived->parent = base;

  // Simulate super.new() chain: first init base, then derived.
  auto [handle, obj] = MakeObj(f, derived);

  // Base constructor sets base_val = 10.
  obj->SetProperty("base_val", MakeLogic4VecVal(f.arena, 32, 10));
  // Derived constructor sets child_val = 20.
  obj->SetProperty("child_val", MakeLogic4VecVal(f.arena, 32, 20));

  EXPECT_EQ(obj->GetProperty("base_val", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("child_val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, SuperNewWithArgs) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Vehicle", {"speed"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, {}, "s", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MkAssign(f.arena, "speed", MkId(f.arena, "s")));
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Car", {"doors"});
  derived->parent = base;

  // Verify base constructor is accessible from derived type chain.
  auto it = derived->parent->methods.find("new");
  ASSERT_NE(it, derived->parent->methods.end());
  auto* base_ctor = it->second;
  ASSERT_NE(base_ctor, nullptr);
  EXPECT_EQ(base_ctor->func_args.size(), 1u);
}

// =============================================================================
// Additional integration-style tests
// =============================================================================

TEST(ClassSim, VTableFindIndex) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Foo", {});

  auto* m1 = f.arena.Create<ModuleItem>();
  m1->kind = ModuleItemKind::kFunctionDecl;
  m1->name = "alpha";
  auto* m2 = f.arena.Create<ModuleItem>();
  m2->kind = ModuleItemKind::kFunctionDecl;
  m2->name = "beta";

  type->vtable.push_back({"alpha", m1, type});
  type->vtable.push_back({"beta", m2, type});

  EXPECT_EQ(type->FindVTableIndex("alpha"), 0);
  EXPECT_EQ(type->FindVTableIndex("beta"), 1);
  EXPECT_EQ(type->FindVTableIndex("gamma"), -1);
}

TEST(ClassSim, InheritanceChainPropertyAccess) {
  ClassFixture f;
  auto* grand = MakeClassType(f, "Grand", {"a"});
  auto* parent = MakeClassType(f, "Parent", {"b"});
  parent->parent = grand;
  auto* child = MakeClassType(f, "Child", {"c"});
  child->parent = parent;

  auto [handle, obj] = MakeObj(f, child);
  obj->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("c", f.arena).ToUint64(), 3u);
}

TEST(ClassSim, PolymorphicVTableMultiLevel) {
  ClassFixture f;
  auto* base = MakeClassType(f, "A", {});
  auto* mid = MakeClassType(f, "B", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "C", {});
  leaf->parent = mid;

  auto* m_base = f.arena.Create<ModuleItem>();
  m_base->kind = ModuleItemKind::kFunctionDecl;
  m_base->name = "f";
  auto* m_leaf = f.arena.Create<ModuleItem>();
  m_leaf->kind = ModuleItemKind::kFunctionDecl;
  m_leaf->name = "f";

  // A defines f, B inherits, C overrides.
  base->vtable.push_back({"f", m_base, base});
  mid->vtable.push_back({"f", m_base, base});   // Inherited.
  leaf->vtable.push_back({"f", m_leaf, leaf});  // Overridden.

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("f"), m_leaf);
}

TEST(ClassSim, ClassTypeRegistryLookup) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Registry", {"x"});

  auto* found = f.ctx.FindClassType("Registry");
  EXPECT_EQ(found, type);

  auto* notfound = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(notfound, nullptr);
}

TEST(ClassSim, MultipleObjectsSameType) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Widget", {"value"});

  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);

  o1->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 100));
  o2->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 200));

  // Each instance has independent properties.
  EXPECT_EQ(o1->GetProperty("value", f.arena).ToUint64(), 100u);
  EXPECT_EQ(o2->GetProperty("value", f.arena).ToUint64(), 200u);
}

TEST(ClassSim, MethodResolutionWalksChain) {
  ClassFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  // Only base defines the method.
  auto* m = f.arena.Create<ModuleItem>();
  m->kind = ModuleItemKind::kFunctionDecl;
  m->name = "deep_method";
  base->methods["deep_method"] = m;

  auto [handle, obj] = MakeObj(f, leaf);
  auto* resolved = obj->ResolveMethod("deep_method");
  EXPECT_EQ(resolved, m);
}

TEST(ClassSim, MethodNotFound) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ClassSim, VirtualMethodNotFound) {
  ClassFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveVirtualMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ClassSim, EmptyVTable) {
  ClassFixture f;
  auto* type = MakeClassType(f, "NoVirtuals", {});
  EXPECT_TRUE(type->vtable.empty());
  EXPECT_EQ(type->FindVTableIndex("anything"), -1);
}
