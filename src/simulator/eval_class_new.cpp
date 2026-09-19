#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_array.h"
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

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      ClassObject* obj, SimContext& ctx,
                                      Arena& arena) {
  for (const auto& prop : info->properties) {
    // §8.9: a static property is one shared copy that lives on the class type,
    // created and initialized once. Constructing an object must not give it a
    // private per-instance copy, or instance-qualified access would shadow the
    // shared storage. Leave static properties out of the instance map so reads
    // and writes fall through to the type's shared static_properties.
    if (prop.is_static) continue;
    // §8.7: a property is initialized to its explicit default if one is given,
    // otherwise to its type's uninitialized value — X for a 4-state type, 0 for
    // a 2-state one — rather than being forced to zero.
    Logic4Vec val;
    if (prop.init_expr) {
      // §6.8 executes a declaration's initializer as an assignment to the
      // declared object, so it is coerced into the property exactly as a later
      // write to it is. The two arms below already size from prop.width, which
      // is what made this one's silence visible.
      val = CoerceToPropertyType(info, prop.name,
                                 EvalExpr(prop.init_expr, ctx, arena), arena);
    } else if (prop.is_4state) {
      val = MakeAllX(arena, prop.width);
    } else {
      val = MakeLogic4VecVal(arena, prop.width, 0);
    }
    StoreClassPropertyDefault(info, prop, val, obj, arena);
  }

  if (info->decl) {
    for (const auto& [pname, pexpr] : info->decl->params) {
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
        auto val = OwnRhsWords(EvalExpr(pexpr, ctx, arena), arena);
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

// Constructs the `info` level of `obj` in the order §8.7 gives: the level's
// constructor formals are bound, its base class is constructed with the
// actuals BaseConstructorActuals answers, then the level's own properties are
// initialized -- after the base constructor, so a default such as `d2 = c2`
// reads what it wrote -- and then the rest of the constructor body runs, its
// leading `super.new` doing nothing more (IsSuperNewRunByConstruction). A
// level with no constructor has the implicit one: the base call and the
// property initialization alone. The level's class is pushed while the base's
// actuals are bound and the body runs, as §8.15 has `super` and the names of
// shadowed members resolve against the lexically enclosing class.
static void ConstructLevel(const ClassTypeInfo* info, ClassObject* obj,
                           ConstructorActuals actuals, const Expr* new_expr,
                           SimContext& ctx, Arena& arena) {
  const ModuleItem* ctor = ClassConstructor(info);
  if (ctor) {
    ctx.PushScope();
    if (actuals.args && actuals.are_callers) {
      BindCallerConstructorArgs(ctor, actuals.args, ctx, arena);
    } else if (actuals.args) {
      BindFunctionArgs(ctor, actuals.args, ctx, arena);
    }
  }
  ctx.PushMethodClass(info);
  if (info->parent) {
    ConstructLevel(info->parent, obj,
                   BaseConstructorActuals(info, ctor, new_expr, arena),
                   new_expr, ctx, arena);
  }
  InitClassPropertyDefaults(info, obj, ctx, arena);
  if (ctor) {
    Variable dummy;
    ExecFunctionBody(ctor, &dummy, ctx, arena);
  }
  ctx.PopMethodClass();
  if (ctor) ctx.PopScope();
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
  ConstructLevel(info, obj, {new_expr, true}, new_expr, ctx, arena);
  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

}  // namespace delta
