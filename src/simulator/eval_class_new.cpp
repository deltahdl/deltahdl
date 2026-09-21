#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// Stores `val` as the initial value of `prop` on `obj`: §7.4.2 has a
// property declared as an array hold its elements one by one, each
// initialized as the one value would be, and §7.5 one declared with a
// dynamic dimension hold no element until `new[]` sizes it; any other
// property is stored under its bare and its class-scoped name.
static void StoreClassPropertyDefault(const ClassTypeInfo* info,
                                      const ClassTypeInfo::PropertyInfo& prop,
                                      const Logic4Vec& val, ClassObject* obj,
                                      Arena& arena) {
  if (prop.is_dynamic) {
    obj->properties[ClassArraySizeKey(prop.name)] =
        MakeLogic4VecVal(arena, 32, 0);
    return;
  }
  if (prop.array_size > 0) {
    for (uint32_t i = 0; i < prop.array_size; ++i) {
      obj->properties[ClassArrayElementKey(prop.name, prop.array_lo + i)] =
          OwnRhsWords(val, arena);
    }
    return;
  }
  obj->properties[std::string(prop.name)] = val;
  std::string scoped = std::string(info->name) + "::" + std::string(prop.name);
  obj->properties[scoped] = val;
}

// §8.12: the object `new src` copies, the one `src` names, shallow-copied as
// TryExecClassShallowCopy in statement_assign_decl.cpp copies it for a
// variable; null where the initializer names no source or no object.
static ClassObject* ShallowCopyOfNewSource(const Expr* init, SimContext& ctx,
                                           Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return nullptr;
  auto* src = ctx.GetClassObject(EvalExpr(init->lhs, ctx, arena).ToUint64());
  return src ? src->ShallowCopy(arena) : nullptr;
}

// §8.7: the `new` initializer of a class-typed property -- `baseA a = new;`,
// `= new(7)` or §8.12's `= new src` -- constructs an object of the property's
// declared class, or shallow-copies the one `src` names, and answers its
// handle through `out`. A bare `new` names no class of its own, so evaluating
// it as an ordinary expression constructs nothing and left the property a
// null handle; the declared type supplies the class, as TryLowerClassNewVarInit
// in lowerer_var.cpp and TryExecClassVarDecl in statement_assign_decl.cpp do
// for a variable. The actuals are bound with the enclosing object as `this`
// (BindCallerConstructorArgs), so `= new(i)` reads the enclosing object's `i`.
// §8.25: the declared class may be named by a type parameter of the level
// `info`, `T obj = new`, which PropertyClassName reads through the object
// under construction's specialization. False for any other initializer, or
// for a property of no class type.
static bool TryInitClassPropertyNew(const ClassTypeInfo* info,
                                    const ClassTypeInfo::PropertyInfo& prop,
                                    SimContext& ctx, Arena& arena,
                                    Logic4Vec& out) {
  const Expr* init = prop.init_expr;
  if (init->kind != ExprKind::kCall || init->text != "new") return false;
  std::string_view class_name =
      PropertyClassName(ctx.CurrentThis(), info, prop.name, ctx);
  if (class_name.empty()) return false;
  if (ClassObject* copy = ShallowCopyOfNewSource(init, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 64, ctx.AllocateClassObject(copy));
    return true;
  }
  out = EvalClassNew(class_name, init, ctx, arena, init->range.start);
  return true;
}

// §8.25: the type each type parameter of one level of the object's class
// chain is bound to on the object under construction, by the parameter's
// name: the object's own level as TypeParamActual reads it (OwnTypeBindings),
// a base level as the extends clause of the level below binds it
// (BaseTypeBindings).
using TypeBindings = std::unordered_map<std::string_view, const DataType*>;

// §8.7's object under construction, with the `new` call that asked for it and
// the run it is built in, carried through the levels of its class chain.
struct Construction {
  ClassObject* obj;
  const Expr* new_expr;
  SimContext& ctx;
  Arena& arena;
  // The bindings of the level being constructed, ConstructBaseThenDefaults
  // swapping a base level's in for the base's construction and back after.
  TypeBindings types;
};

// §8.25: the bindings of the object's own class -- the actual its
// specialization bound each type parameter to, or the default the class
// declares (§8.25.1).
static TypeBindings OwnTypeBindings(const ClassObject* obj) {
  TypeBindings bindings;
  const ClassDecl* decl = obj->type->decl;
  if (decl == nullptr) return bindings;
  for (const auto& [pname, pexpr] : decl->params) {
    if (decl->type_param_names.count(pname) == 0) continue;
    if (const DataType* actual = TypeParamActual(obj, decl, pname))
      bindings[pname] = actual;
  }
  return bindings;
}

// §8.25: the type actuals the extends clause of `child` gives its base's type
// parameters: the `#(...)` list written after the base's name, or, where the
// base is named by one of the child's own type parameters -- `class D4 #(type
// P = C#(byte)) extends P;` (printed page 205 of IEEE 1800-2023) -- the
// list the type that parameter is bound to on this object carries, `byte` for
// D4's default specialization and `int` under `extends D4 #(C#(int))`. Null
// where such a parameter is bound to nothing, which leaves the base at its
// defaults.
static const std::vector<DataType>* BaseTypeActuals(
    const ClassDecl* child, const TypeBindings& child_types) {
  if (child->type_param_names.count(child->base_class) == 0)
    return &child->base_class_type_params;
  auto bound = child_types.find(child->base_class);
  return bound == child_types.end() ? nullptr : &bound->second->type_params;
}

// §8.25: the bindings of the base level `base` of a level declared by
// `child`, whose extends clause binds the base's type parameters as a
// specialization does -- `extends C` takes C's defaults, `extends C
// #(integer)` binds integer, and `extends C #(P)` binds what the child's own
// parameter P is bound to on this object (printed page 204 of IEEE
// 1800-2023), so an actual naming one of the child's type parameters is
// read through the child's bindings.
static TypeBindings BaseTypeBindings(const ClassDecl* child,
                                     const TypeBindings& child_types,
                                     const ClassTypeInfo* base) {
  TypeBindings bindings;
  const ClassDecl* decl = base->decl;
  if (decl == nullptr || child == nullptr) return bindings;
  const std::vector<DataType>* actuals = BaseTypeActuals(child, child_types);
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual =
        actuals == nullptr ? nullptr : ActualForParam(*actuals, i, pname);
    if (actual == nullptr) {
      actual = TypeParamActual(nullptr, decl, pname);
    } else if (actual->kind == DataTypeKind::kNamed) {
      auto bound = child_types.find(actual->type_name);
      if (bound != child_types.end()) actual = bound->second;
    }
    if (actual != nullptr) bindings[pname] = actual;
  }
  return bindings;
}

// §8.25: the width of the property `prop` of the level being constructed
// where its declared type names a type parameter of that level, sized by the
// type the parameter is bound to; the collector's width otherwise.
// CollectClassMembers in lowerer_class.cpp sizes a property by the class's
// declaration alone, so `T x` carries 32 bits whatever T is bound to.
static uint32_t BoundPropertyWidth(const ClassTypeInfo::PropertyInfo& prop,
                                   const Construction& c) {
  if (prop.width_is_declared || prop.type_name.empty()) return prop.width;
  auto bound = c.types.find(prop.type_name);
  if (bound == c.types.end()) return prop.width;
  uint32_t width = DeclaredTypeWidth(*bound->second, c.ctx);
  return width != 0 ? width : prop.width;
}

// §8.7: the property `prop` of the level `info` of `obj` initialized to its
// explicit default if one is given, otherwise to its type's uninitialized
// value — X for a 4-state type, 0 for a 2-state one — rather than being
// forced to zero.
static void InitClassPropertyDefault(const ClassTypeInfo* info,
                                     const ClassTypeInfo::PropertyInfo& prop,
                                     Construction& c) {
  ClassObject* obj = c.obj;
  SimContext& ctx = c.ctx;
  Arena& arena = c.arena;
  // §7.10/§8.7: a queue property with an initializer, `int q[$] = {1, 2}`,
  // takes the initializer's elements as its own, and holds no value under
  // its name. One without an initializer is left to ClassQueueProperty,
  // which builds it empty on the first reference, once the specialization's
  // parameters, which its bound may name (§8.25), are bound to the object.
  if (prop.init_expr != nullptr &&
      InitClassQueueProperty(obj, info, prop.name, prop.init_expr, ctx)) {
    return;
  }
  // §15.3.1 (printed page 373 of IEEE 1800-2023) and §15.4.1 (printed
  // 374) with §8.7: a semaphore or mailbox property's `new` builds the object's
  // own bucket or queue (ClassObject::semaphore_properties and
  // mailbox_properties) and stores the handle's carrier under the name,
  // nonzero for a property holding an object, which §8.4 (printed 181-182)
  // compares with null; evaluated as a value, the `new` built nothing, and a
  // 0 stored here after the build read a property holding a mailbox as null.
  if (TryInitClassSyncProperty(obj, info, prop.name, prop.init_expr, ctx))
    return;
  Logic4Vec val;
  if (prop.init_expr && TryInitClassPropertyNew(info, prop, ctx, arena, val)) {
    StoreClassPropertyDefault(info, prop, val, obj, arena);
    return;
  }
  if (prop.init_expr) {
    // §6.8 executes a declaration's initializer as an assignment to the
    // declared object, so it is coerced into the property exactly as a later
    // write to it is. The two arms below already size from prop.width, which
    // is what made this one's silence visible.
    //
    // §11.6.1 with §11.8.2: the initializer is the right-hand side of that
    // assignment, so the property's declared width sizes its
    // context-determined operands before the operators are applied, as
    // Lowerer::LowerVarInit sizes a module variable's. Evaluated
    // self-determined and widened after, `logic [15:0] v = -8'd6` negated at
    // 8 bits and read 00fa where the clause gives fffa. A property whose
    // width the declaration did not settle, or a real one, is evaluated
    // self-determined and converted by CoerceToPropertyType as before.
    uint32_t context_width = prop.width_is_declared && !prop.is_real
                                 ? BoundPropertyWidth(prop, c)
                                 : 0;
    val = CoerceToPropertyType(
        info, prop.name, EvalExpr(prop.init_expr, ctx, arena, context_width),
        arena);
  } else if (prop.is_4state) {
    val = MakeAllX(arena, BoundPropertyWidth(prop, c));
  } else {
    val = MakeLogic4VecVal(arena, BoundPropertyWidth(prop, c), 0);
  }
  StoreClassPropertyDefault(info, prop, val, obj, arena);
}

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      Construction& c) {
  ClassObject* obj = c.obj;
  SimContext& ctx = c.ctx;
  Arena& arena = c.arena;
  for (const auto& prop : info->properties) {
    // §8.9: a static property is one shared copy that lives on the class type,
    // created and initialized once. Constructing an object must not give it a
    // private per-instance copy, or instance-qualified access would shadow the
    // shared storage. Leave static properties out of the instance map so reads
    // and writes fall through to the type's shared static_properties.
    if (prop.is_static) continue;
    InitClassPropertyDefault(info, prop, c);
  }

  if (info->decl) {
    // §8.25 with §6.20.2: each default is sized by the parameter's declared
    // type (ClassParamSizer), as the class's own copy is (InitClassParams in
    // lowerer_class.cpp).
    ClassParamSizer sizer(info->decl);
    const auto& params = info->decl->params;
    for (size_t i = 0; i < params.size(); ++i) {
      const auto& [pname, pexpr] = params[i];
      if (pexpr) {
        // §6.8 makes the object's stored parameter and whatever the default
        // expression read two data storage elements, each storing "a value
        // from one assignment to the next". EvalExpr on a bare identifier
        // answers with the variable's own vector (evaluation.cpp), and a
        // Logic4Vec copy carries the words pointer rather than the words
        // (src/common/types.h), so storing it as it arrived left the two as
        // one buffer. The property arm above reaches the same copy through
        // CoerceToPropertyType; this arm coerces nothing, so it takes it here.
        // The bare and the scoped key are two names for the one parameter and
        // every writer sets both, so they share the one copy as they do above.
        auto val = OwnRhsWords(sizer.Value(i, pexpr, ctx, arena), arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped =
            std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
  }
}

// §8.7: the actuals of a `new(...)` call are the caller's expressions, so they
// are bound with the caller's `this` and class in force, the object under
// construction taken off the stack for the binding and put back after:
// `next = new(depth - 1)` in a method of the class reads the method's own
// object, where with the fresh object on top it read that object's `depth`,
// still at its default, and constructed a chain that never ended.
static void BindCallerConstructorArgs(const ModuleItem* ctor,
                                      const Expr* args_expr, SimContext& ctx,
                                      Arena& arena) {
  ClassObject* constructed = ctx.CurrentThis();
  ctx.PopThis();
  BindFunctionArgs(ctor, args_expr, ctx, arena);
  ctx.PushThis(constructed);
}

// The actuals one level's constructor is called with. `are_callers` says they
// are the `new` call's own, the caller's expressions; otherwise they are
// expressions of the derived class's constructor -- its leading `super.new`
// call or its extends specifier -- and read the object under construction and
// the derived constructor's formals.
struct ConstructorActuals {
  const Expr* args = nullptr;
  bool are_callers = false;
};

static const ModuleItem* ClassConstructor(const ClassTypeInfo* info) {
  auto it = info->methods.find("new");
  return it == info->methods.end() ? nullptr : it->second;
}

// The `super.new(...)` call standing as the first statement of `ctor`, the
// form §8.15 requires of an explicit base constructor call, or null. The
// declarations of the body's locals stand ahead of its statements (A.2.8's
// block_item_declaration, `uvm_report_handler rh;` before uvm_root::new's
// `super.new("__top__", null)`), and are no statement, so they are passed
// over.
static const Expr* LeadingSuperNewCall(const ModuleItem* ctor) {
  if (!ctor) return nullptr;
  const Stmt* first = nullptr;
  for (const Stmt* s : ctor->func_body_stmts) {
    if (s && s->kind == StmtKind::kVarDecl) continue;
    first = s;
    break;
  }
  if (!first || first->kind != StmtKind::kExprStmt || !first->expr)
    return nullptr;
  const Expr* call = first->expr;
  if (call->kind != ExprKind::kCall) return nullptr;
  MethodCallParts parts;
  if (!ExtractMethodCallParts(call, parts)) return nullptr;
  if (parts.var_name != "super" || parts.method_name != "new") return nullptr;
  return call;
}

// §8.17: the `super.new(default)` form, whose one argument is the keyword.
static bool IsSuperNewDefault(const Expr* call) {
  return call->args.size() == 1 && call->args[0] &&
         call->args[0]->kind == ExprKind::kIdentifier &&
         call->args[0]->text == "default";
}

bool IsSuperNewRunByConstruction(const Expr* call, SimContext& ctx) {
  if (IsSuperNewDefault(call)) return true;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) return false;
  return call == LeadingSuperNewCall(ClassConstructor(enclosing));
}

static size_t FindFirstDefaultArgPos(const ModuleItem* method) {
  for (size_t j = 0; j < method->func_args.size(); ++j) {
    if (method->func_args[j].is_default) {
      return j;
    }
  }
  return 0;
}

static size_t FindChildNewDefaultPos(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return FindFirstDefaultArgPos(m->method);
    }
  }
  return 0;
}

static const Expr* SynthDefaultExtendsArgs(const ClassTypeInfo* base,
                                           const ClassDecl* child_decl,
                                           const Expr* new_expr, Arena& arena) {
  size_t default_pos = FindChildNewDefaultPos(child_decl);

  size_t base_argc = 0;
  const ModuleItem* base_ctor = ClassConstructor(base);
  if (base_ctor) base_argc = base_ctor->func_args.size();
  auto* synth = arena.Create<Expr>();
  synth->kind = ExprKind::kCall;
  for (size_t j = 0; j < base_argc && default_pos + j < new_expr->args.size();
       ++j) {
    synth->args.push_back(new_expr->args[default_pos + j]);
  }
  return synth;
}

// §8.17: whether the child class's own 'new' constructor argument list uses the
// 'default' keyword. When it does, the trailing actuals of the derived-most
// new() call expand to the superclass constructor's argument list.
static bool ChildNewUsesDefaultArg(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      for (const auto& a : m->method->func_args) {
        if (a.is_default) return true;
      }
      return false;
    }
  }
  return false;
}

// §8.15/§8.17: the actuals `info`'s base class constructor is called with.
// A `super.new(...)` standing as the first statement of `info`'s constructor
// passes its own arguments, evaluated in that constructor's scope with its
// formals bound; the `super.new(default)` form and a constructor that uses
// `default` without the call forward the `new` call's trailing actuals, the
// caller's expressions; an extends specifier with arguments passes those; and
// with none of them the base constructor is called with no arguments.
static ConstructorActuals BaseConstructorActuals(const ClassTypeInfo* info,
                                                 const ModuleItem* ctor,
                                                 const Expr* new_expr,
                                                 Arena& arena) {
  const Expr* leading = LeadingSuperNewCall(ctor);
  if (leading && !IsSuperNewDefault(leading)) return {leading, false};
  const ClassDecl* decl = info->decl;
  if (!decl) return {};
  if (!decl->extends_args.empty()) {
    auto* synth = arena.Create<Expr>();
    synth->kind = ExprKind::kCall;
    synth->args = decl->extends_args;
    return {synth, false};
  }
  if ((decl->extends_has_default || ChildNewUsesDefaultArg(decl)) && new_expr) {
    return {SynthDefaultExtendsArgs(info->parent, decl, new_expr, arena), true};
  }
  return {};
}

// Binds the level's constructor formals in a scope of their own, from the
// caller's actuals or from the ones the level below handed up.
static void BindLevelFormals(const ModuleItem* ctor, ConstructorActuals actuals,
                             SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  if (!actuals.args) return;
  if (actuals.are_callers) {
    BindCallerConstructorArgs(ctor, actuals.args, ctx, arena);
  } else {
    BindFunctionArgs(ctor, actuals.args, ctx, arena);
  }
}

// §8.7 and §13.5: a constructor's arguments follow the ordinary subroutine
// conventions, so when the level's constructor returns each `output` or
// `inout` formal is copied into the actual it was bound from, the level's
// scope still on top for WritebackOutputArgs to take off. The caller's
// actuals -- the `new` call's own, or the trailing ones §8.17's `default`
// forwards to the base -- are the caller's expressions, so they are assigned
// with the caller's `this` in force, as BindCallerConstructorArgs bound them;
// a `super.new(oid)` actual is the derived constructor's own and is assigned
// into its scope, from where the derived level copies it out in turn.
static void WritebackLevelFormals(const ModuleItem* ctor,
                                  ConstructorActuals actuals, SimContext& ctx,
                                  Arena& arena) {
  if (!actuals.args) return;
  if (!actuals.are_callers) {
    WritebackOutputArgs(ctor, actuals.args, ctx, arena);
    return;
  }
  ClassObject* constructed = ctx.CurrentThis();
  ctx.PopThis();
  WritebackOutputArgs(ctor, actuals.args, ctx, arena);
  ctx.PushThis(constructed);
}

static void ConstructLevel(const ClassTypeInfo* info,
                           ConstructorActuals actuals, Construction& c);

// The base of `info`, constructed with the actuals its constructor names for
// it, then the level's own properties initialized; the whole of the implicit
// constructor and the head of an explicit one.
static void ConstructBaseThenDefaults(const ClassTypeInfo* info,
                                      const ModuleItem* ctor, Construction& c) {
  if (info->parent) {
    TypeBindings own = std::move(c.types);
    c.types = BaseTypeBindings(info->decl, own, info->parent);
    ConstructLevel(info->parent,
                   BaseConstructorActuals(info, ctor, c.new_expr, c.arena), c);
    c.types = std::move(own);
  }
  // §8.7 with §23.9 and §26.3: a property initializer is an expression of
  // the class declaration's scope, nested in the package, module or unit
  // declaring the class and never in the body constructing the object, so
  // the defaults are read in a frame of their own marked a subroutine's, at
  // which the package search ends (SimContext::PackageFrame): a package
  // class's frame carries the package, whose enum literals, parameters and
  // variables the initializer names bare (§26.2), and a module or unit
  // class's carries none, so `int x = five()` is the module's five and not
  // the one a constructing body's own import supplies. The frame is pushed
  // after the base is constructed, so a base of another scope reads its own.
  // A specialization's value parameters, bound as locals of the frame the
  // `C#(7)::new` call pushed (BindClassParams), are bound again in this
  // frame (CollectClassParamBindings): the mark ends the search for a local
  // at this frame too (§23.9), so `int x = W` under `C#(7)::new` reads the
  // 7 here or nowhere.
  auto params = CollectClassParamBindings(info, c.ctx);
  c.ctx.PushScope();
  RebindClassParamBindings(params, c.ctx);
  c.ctx.EnterSubroutineScope(info->package);
  InitClassPropertyDefaults(info, c);
  c.ctx.PopScope();
}

// Constructs the `info` level of the object in the order §8.7 gives: the
// level's constructor formals are bound, its base class is constructed with
// the actuals BaseConstructorActuals answers, then the level's own properties
// are initialized -- after the base constructor, so a default such as
// `d2 = c2` reads what it wrote -- and then the rest of the constructor body
// runs, its leading `super.new` doing nothing more
// (IsSuperNewRunByConstruction), and its output formals are copied out
// (WritebackLevelFormals). A level with no constructor has the implicit
// one: the base call and the property initialization alone. The level's class
// is pushed while the base's actuals are bound and the body runs, as §8.15 has
// `super` and the names of shadowed members resolve against the lexically
// enclosing class.
static void ConstructLevel(const ClassTypeInfo* info,
                           ConstructorActuals actuals, Construction& c) {
  const ModuleItem* ctor = ClassConstructor(info);
  // §8.25: the constructor body reads the specialization's parameters the
  // `C#(7)::new` call bound as the property defaults do, so they are bound
  // again in the frame BindLevelFormals pushes (CollectClassParamBindings).
  auto params = CollectClassParamBindings(info, c.ctx);
  if (ctor) {
    BindLevelFormals(ctor, actuals, c.ctx, c.arena);
    RebindClassParamBindings(params, c.ctx);
  }
  c.ctx.PushMethodClass(info);
  ConstructBaseThenDefaults(info, ctor, c);
  if (ctor) {
    // §26.2: the constructor body reads the package's names bare as any
    // method does (ExecClassMethod); the frame is the one BindLevelFormals
    // pushed, given the package once the base, whose own frames stood above
    // it meanwhile, is constructed.
    c.ctx.EnterSubroutineScope(info->package);
    Variable dummy;
    ExecFunctionBody(ctor, &dummy, c.ctx, c.arena);
    WritebackLevelFormals(ctor, actuals, c.ctx, c.arena);
  }
  c.ctx.PopMethodClass();
  if (ctor) c.ctx.PopScope();
}

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena, SourceLoc loc) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of abstract class '" +
                            std::string(class_type) + "'",
                        Subclause("8.21"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of interface class '" +
                            std::string(class_type) + "'",
                        Subclause("8.26.5"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;
  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);
  Construction construction{obj, new_expr, ctx, arena, OwnTypeBindings(obj)};
  ConstructLevel(info, {new_expr, true}, construction);
  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

}  // namespace delta
