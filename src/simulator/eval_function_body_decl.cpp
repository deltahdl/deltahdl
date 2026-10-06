#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/covergroup_instance.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/static_aggregate.h"
#include "simulator/sync_variable.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

// §13.3 and §13.4 with §6.8: a variable declaration in a subroutine body --
// the local's storage at its declared type's width, its kinds (4-state,
// signed, string, class, virtual interface, enumeration, layout), Table 6-7's
// default, its initializer as an assignment to it, and the static (§13.4.2)
// or automatic lifetime that says whether one copy is kept across calls.
// Moved out of eval_function_body.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at.

// §6.18 with §7.2.1: a variable declared by a typedef name is an object of
// the type the name stands for, and a member read or write of it is a window
// of that type's layout, which SimContext resolves through the layout bound
// to the variable's name (ResolveMemberByType, ResolveFieldTarget). The
// layout a typedef name stands for is registered under that name by
// RegisterDesignTypeLayouts, so the variable's name is bound to it, as a
// declared variable's is by Lowerer::LowerVar. Answers whether the name
// stands for a layout at all; a type that is no structure or union -- or one
// written inline, which has no name the table could hold -- binds nothing.
// The subroutine's implicit variable (BindReturnStructLayout) and a body
// local (BindLocalAggregateLayout) are bound through here alike.
//
// §8.23 with §7.2: a structure typedef a class declares is registered under
// "C::S", its name with the class's, and a variable declared with it names
// it so, `P2::S v` in a module's function, or bare, `S v` or a function
// returning `S` in a method of the class or of one extending it. Asked by the
// bare name alone, neither was bound, and every member written to it was
// lost. A specialization's methods read the class's typedef as the
// specialization binds it, which the declaration's own layout does not hold,
// so only the class itself, its default specialization, is asked. A class
// with a value parameter has its typedef folded with the running
// specialization's values instead (MethodClassTypedefLayout).
static std::string_view NamedLayoutKey(const DataType& type, SimContext& ctx) {
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  auto key_in = [&](std::string_view scope) -> std::string_view {
    auto* key = ctx.GetArena().Create<std::string>(std::string(scope) +
                                                   "::" + std::string(name));
    return ctx.FindStructType(*key) != nullptr ? std::string_view(*key)
                                               : std::string_view{};
  };
  if (!type.scope_name.empty())
    return type.type_params.empty() ? key_in(type.scope_name)
                                    : std::string_view{};
  if (ctx.FindStructType(name) != nullptr) return name;
  std::string_view specialized;
  if (MethodClassTypedefLayout(name, ctx, &specialized) != nullptr)
    return specialized;
  for (const ClassTypeInfo* c = ctx.CurrentMethodClass(); c != nullptr;
       c = c->parent) {
    if (c->param_actuals != nullptr) return {};
    if (std::string_view key = key_in(c->name); !key.empty()) return key;
  }
  return {};
}

bool BindNamedLayout(std::string_view var_name, const DataType& type,
                     SimContext& ctx) {
  std::string_view type_name = NamedLayoutKey(type, ctx);
  if (type_name.empty()) return false;
  ctx.SetVariableStructType(var_name, type_name);
  return true;
}

// §13.3 (printed page 337) runs a subroutine body's statements as a
// begin-end group's, declarations included, and §11.9 (printed 304) lets a
// tagged union variable be initialized with a tagged union expression, whose
// value §7.3.2 (printed 151) has carry the member's tag beside its bits. A
// body local declared by a typedef name was bound to no layout and, with a
// `tagged` initializer, to no tag: `u_t v = tagged Valid -7;` inside a
// function left `v.Valid` read through no member, and `return v;` handed
// the caller the bits with no tag, RecordReturnedVariableTag gating on the
// local's layout being a union. The layout is bound as the return type's is,
// and the tag set as Lowerer::LowerVar sets a module-scope declaration's and
// AssignToScalarLhs a `v = tagged M x` statement's -- under the local's own
// name, which is the key TagKeyOfName resolves a local to, so the body's
// reads, the return and a later assignment all find one tag.
static void BindLocalAggregateLayout(std::string_view name,
                                     const DataType& type, const Expr* init,
                                     SimContext& ctx) {
  if (!BindNamedLayout(name, type, ctx)) return;
  if (init != nullptr && init->kind == ExprKind::kTagged &&
      init->rhs != nullptr) {
    ctx.SetVariableTag(name, init->rhs->text);
  }
}

// §11.9 (printed page 304) lets a tagged union variable be initialized with
// a tagged union expression whose braces are a §10.9.2 structure assignment
// pattern, and §10.9.2 (printed 263) evaluates each member expression in the
// context of an assignment to the member it initializes, by position or by
// name. A body local's `tagged Add '{3, 8'd4}` was evaluated as any
// expression is, with no layout to place the pattern by, so its elements
// were concatenated in written order at their self-determined widths -- the
// byte 4 below the 3, `'{b: 4, a: 3}` swapped -- and `v.Add.a` read through
// the member's window found the wrong bits, where the statement `v = tagged
// Add '{...}` is placed by the member's layout (EvalRhsWithStructContext) and
// an actual `f(tagged Add '{...})` by the formal's (TryEvalPatternActual).
// TaggedPatternMemberLayout answers, through the TaggedMemberLayout those two
// share, the member's layout within the union the local's typedef name
// registers, and null where the initializer is no tagged expression over a
// pattern, bare or typed, the type names no layout, or the member has none of
// its own; EvalLocalInitializer places the pattern by that layout and
// evaluates any other initializer as it was.
static const StructTypeInfo* TaggedPatternMemberLayout(const DataType& type,
                                                       const Expr* init,
                                                       SimContext& ctx) {
  if (init->kind != ExprKind::kTagged || init->rhs == nullptr ||
      init->lhs == nullptr ||
      UnwrapTypedPattern(init->lhs)->kind != ExprKind::kAssignmentPattern)
    return nullptr;
  const StructTypeInfo* layout = ctx.FindStructType(type.type_name);
  return layout != nullptr ? TaggedMemberLayout(*layout, init->rhs->text)
                           : nullptr;
}

static Logic4Vec EvalLocalInitializer(const DataType& type, const Expr* init,
                                      SimContext& ctx, Arena& arena) {
  if (const StructTypeInfo* member =
          TaggedPatternMemberLayout(type, init, ctx)) {
    return EvalStructPatternValue(UnwrapTypedPattern(init->lhs), member, ctx,
                                  arena);
  }
  return EvalExpr(init, ctx, arena);
}

// §6.8 (Table 6-7): a 4-state local starts as 'x whatever the subroutine's
// lifetime (§13.3, §13.4), as Lowerer::LowerVar starts a module's. Created
// at 0 by CreateLocalVariable, a body's `logic l;` read 0 where the module's
// read x. A handle and a virtual interface are no 4-state values and keep
// the 0 that is null, and a string, created with no width, keeps its "".
static void FillLocalDefault(Variable* v, bool has_initializer,
                             bool holds_a_handle, Arena& arena) {
  if (has_initializer || !v->is_4state || holds_a_handle || v->is_string)
    return;
  v->value = MakeAllX(arena, v->value.width);
  v->value.is_signed = v->is_signed;
}

// §10.7 sizes a declaration's initializer into the declared width; §6.12.1
// has one assigned to a real local convert numerically instead, `real l = 2`
// holding 2.0 and a real into a shortreal its single-precision value, where a
// resize would have kept the integer's bits or cut the double's in half.
static Logic4Vec SizeLocalInitializer(const Logic4Vec& val, const Variable& v,
                                      uint32_t declared, Arena& arena) {
  if (v.is_real) return ConvertRealForKnownLhs(val, true, declared, arena);
  return ResizeToWidth(val, declared, arena);
}

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  // A class-typed local (user class, or the built-in `process`/handle types)
  // holds a 64-bit handle and must record its class type so later method calls
  // such as `p.suspend()` dispatch -- module-scope decls do this via
  // TryExecClassVarDecl, but function-body locals take this path instead.
  // §8.23 (printed pages 200-201): the class is the one the run holds under
  // the declaration's spelling, `Outer::Inner` for a nested class named from
  // outside its container (DeclaredClassKey), where a lookup by the bare
  // `Inner` found none, so `Outer::Inner i = new; i.bump();` in a function,
  // a task or a class method declared a plain variable and ran no method.
  std::string_view class_key = DeclaredClassKey(type, ctx, arena);
  bool is_class = !class_key.empty();
  // §25.9: a virtual interface declared in a function body, by the type or
  // by a typedef name standing for it, holds the handle of the instance it
  // represents, as wide as Lowerer::LowerVar makes a variable declared so and
  // as a formal declared so is bound, and is flagged so that a member the
  // body reaches through it, `v.clk` after `v = dif`, is a component of that
  // instance (ResolveVirtualInterfaceBase). Before this, such a local was a
  // 32-bit vector no reader took for a virtual interface, and `v.clk` named
  // nothing.
  bool is_virtual_interface = DeclaresAVirtualInterface(type, ctx);
  bool holds_a_handle = is_class || is_virtual_interface;
  // §6.18: a local declared with a user-defined type name is an object of the
  // type that name stands for, so `nib v` is as wide as `nib` is.
  // DeclaredTypeWidth is what reaches that width; the one-argument
  // EvalTypeWidth gives a DataTypeKind::kNamed no width at all, and the
  // fallback below then made every typedef'd body local 32 bits. This is the
  // site a subroutine body's declaration takes -- the statement executor's own
  // ExecVarDeclImpl serves a declaration outside a subroutine -- so the two
  // have to reach the typedef table separately.
  uint32_t declared = holds_a_handle ? 64 : DeclaredTypeWidth(type, ctx);
  // §6.16: a string has no declared width and starts as "", so it is created
  // with none rather than at the carrier width below, and marked so that what
  // reads a string reads the flag rather than a width. A declaration outside a
  // subroutine does both in CreateDeclVariable; without them here,
  // ExecFuncIdentifierAssign would take the length of whatever the local was
  // last assigned for a declared width and truncate to it. The flag is set on
  // the variable this call created rather than through
  // SimContext::RegisterStringVariable, which resolves a name and would reach a
  // variable of the design that the local shadows.
  bool is_string = !is_class && DeclaredTypeIsString(type, ctx);
  uint32_t w = declared ? declared : (is_string ? 0 : 32);
  // §6.11.3: a body local carries its declared signedness exactly as a
  // module-scope declaration does (Lowerer sets the same flag there), so an
  // `integer` local is a signed operand rather than an unsigned one.
  auto* v = ctx.CreateLocalVariable(name, w, DeclaredTypeIsSigned(type, ctx));
  // §19.3: a local of a covergroup type holds a handle, its instance built by
  // a `new` initializer.
  v->declared_type = &type;
  if (TryCreateCovergroupLocal(type, init, v, ctx, arena)) return v;
  v->is_4state = DeclaredTypeIs4State(type, ctx);
  v->is_virtual_interface = is_virtual_interface;
  if (is_string) v->is_string = true;
  // §6.12: a local declared real, shortreal or realtime, by the keyword or by
  // a typedef name standing for one, is a real variable the body stores into
  // under §6.12.1's conversion and reads as a real, as a formal declared so
  // is (BindValueArg). A declaration outside a subroutine registers its name
  // for the same (CreateDeclVariable); the mark on the variable is what the
  // body's stores read, so `real l; l = a + b;` keeps the real sum rather
  // than rounding it into an integer whose bits the caller read as 0.0.
  v->is_real = !holds_a_handle && DeclaredTypeIsReal(type, ctx);
  // §15.5 with §6.21: a local declared event is a named event of its frame,
  // which `-> le` triggers and `@le` waits on as a module's. Left unmarked,
  // the trigger and the wait took it for a value and neither reached the
  // other.
  v->is_event = type.kind == DataTypeKind::kEvent;
  FillLocalDefault(v, init != nullptr, holds_a_handle, arena);
  if (is_class) {
    ctx.SetVariableClassType(name, class_key);
    // §8.25 (printed pages 203-204): `S #(byte) l` is of the specialization
    // its list names, recorded as a declaration outside a subroutine records
    // it, so its `new` and its static members are S #(byte)'s.
    RecordClassParamActuals(name, class_key, type.type_params, ctx);
  }
  RecordVariableEnumType(name, type, ctx);
  // §11.5.1: the declared range an index of the local resolves against, the
  // dimension written here or the one its typedef name stands for (§6.18),
  // recorded as ExecVarDeclImpl records it for a procedure's declaration; a
  // body local had none and was addressed as [width-1:0] whatever its
  // declaration said.
  if (!holds_a_handle) {
    RecordDeclaredRange(type, v, ctx, arena);
    // §6.18 with §7.3.2: the members the local's typedef name declares, and
    // the tag a `tagged` initializer gives a tagged union local.
    BindLocalAggregateLayout(name, type, init, ctx);
  }
  // §7.2.2: a local of a structure type with no initializer takes the default
  // each member's declaration writes.
  if (init == nullptr) {
    ApplyVariableLayoutDefaults(name, v, ctx, arena);
    return v;
  }
  // §8.4: `P p = new;` creates an object of class P and assigns its handle to
  // p. `new` names a construction, not a value to be read, so evaluating it as
  // an ordinary initializer expression yields no object and leaves the handle
  // null. A class-typed local with a `new` initializer is therefore constructed
  // here, as the declaration path for a variable outside a subroutine does.
  if (is_class && init->kind == ExprKind::kCall && init->text == "new") {
    v->value = EvalClassNew(ctx.GetVariableClassType(name), init, ctx, arena,
                            init->range.start);
    ApplyClassParamOverrides(name, v->value.ToUint64(), ctx, arena);
    return v;
  }
  // §6.8 states a variable declaration assignment as an assignment to the
  // declared variable, so §10.7 truncates or extends the initializer into the
  // width the type declares rather than letting it put its own vector in place:
  // a Logic4Vec carries its own width, and a sized literal is self-determined,
  // so `nib v = 8'hFF` left v eight bits holding 255.
  //
  // The target is the declared width and not the width the variable was created
  // at, because the 32 above is a carrier for a type nothing here could size
  // rather than a width the source asked for. A string local (§6.16) is the
  // case that turns on the difference: it is created at that carrier width and
  // has no declared width at all, and its initializer is what gives it one.
  // ResizeToWidth leaves a value alone at a target of 0, so such a local keeps
  // the behaviour it had.
  //
  // §6.8 also has a variable stand for a data storage element that keeps its
  // value from one assignment to the next. An initializer
  // that reads another variable is answered with that variable's own Logic4Vec,
  // and a Logic4Vec copies its words pointer, so `bit [7:0] y = x;` left y and
  // x one element. The declaration is quiet about it -- nothing writes in place
  // here -- and the next store to y is what shows it: ExecFuncIdentifierAssign
  // coerces a 2-state target in place and cleared x's x/z bits through the
  // shared words. The copy goes outside the resize rather than inside because
  // ResizeToWidth returns its argument untouched when the widths already match,
  // which is precisely the aliased case; outside, it covers every path, and is
  // merely redundant on the path where the resize itself allocated.
  //
  // §11.9: a `tagged M '{...}` initializer is placed by the member's layout
  // (EvalLocalInitializer) before the resize into the union's frame.
  v->value = OwnRhsWords(
      SizeLocalInitializer(EvalLocalInitializer(type, init, ctx, arena), *v,
                           declared, arena),
      arena);
  // §6.11.2: a 4-state value converted automatically to a 2-state one has every
  // unknown or high-impedance bit turned to zero, and
  // §6.8 makes a variable declaration assignment an assignment to the declared
  // variable, so a 2-state local declared from a 4-state initializer holds
  // zeros where that initializer held x or z. The flag was recorded above and
  // applied by nothing on this path: every later store consults it in
  // ExecFuncIdentifierAssign, so `int v; v = seed;` converted where `int v =
  // seed;` did not -- two spellings of one declaration with two answers. The
  // coercion writes in place and so goes after the copy, never through the
  // value the initializer produced: an initializer that reads another variable
  // is answered with that variable's own Logic4Vec, and coercing through it
  // would clear the source's own unknown bits (#3563).
  if (!v->is_4state) CoerceTo2State(v->value);
  return v;
}

// §7.10/§7.4.2: the storage the declaration's own dimensions ask for, which a
// body local needs as much as a declaration outside a subroutine does. The
// variable CreateFuncLocalVar makes carries one element's width, and
// CreateDeclAggregate makes the queue or the elements beside it, which is the
// step the two paths did not share: `int q[$];` in a task body was a plain
// vector, and since the elaborator now gives a procedural declaration the
// dimensions its typedef carries, `q_t qu;` reaches here with the same
// dimensions and the same need.
//
// §10.5 (printed page 256): the initializer of such a declaration is assigned
// to the array made here (AssignDeclAggregateInit) rather than evaluated onto
// the carrier, which CarrierInit keeps it from.
static void CreateFuncLocalAggregate(const Stmt* stmt, Variable* var,
                                     SimContext& ctx, Arena& arena) {
  if (var == nullptr) return;
  CreateDeclAggregate(stmt, var->value.width, ctx, arena);
  AssignDeclAggregateInit(stmt, ctx, arena);
  CreateSyncObjectForLocal(stmt, var, ctx, arena);
}

// The initializer the element-width carrier CreateFuncLocalVar makes takes:
// none where the declaration has unpacked dimensions, the array itself taking
// it in CreateFuncLocalAggregate.
static const Expr* CarrierInit(const Stmt* stmt) {
  return stmt->var_unpacked_dims.empty() ? stmt->var_init : nullptr;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
}

// §13.3.2 (printed page 339) and §13.4.2 (printed 344): the variable of a
// static local is kept in its subroutine's static frame, and the queue,
// associative array or shape its declaration made is kept beside it
// (RetainStaticAggregate); a later call's declaration refers to both again.
static void ExecFuncVarDeclStatic(const Stmt* stmt, std::string_view func_name,
                                  SimContext& ctx, Arena& arena) {
  auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
  if (existing) {
    ctx.AliasLocalVariable(stmt->var_name, existing);
    RestoreStaticAggregate(func_name, stmt->var_name, ctx);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
  ctx.SaveStaticFuncVar(func_name, stmt->var_name, v);
  RetainStaticAggregate(func_name, stmt->var_name, ctx, arena);
}

// §6.23 with §8.11: `var static type(this) m_inst;` in a method declares a
// handle of the class the method belongs to, so the declaration is taken as
// one naming that class. Left as written, its type was implicit and m_inst a
// one-bit variable no `new` could store an object in. Any other declaration
// is returned as it is.
static const Stmt* DeclOfThisTypeRef(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  const Expr* ref = stmt->var_decl_type.type_ref_expr;
  if (ref == nullptr || ref->kind != ExprKind::kIdentifier ||
      ref->text != "this")
    return stmt;
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (cls == nullptr) return stmt;
  auto* copy = arena.Create<Stmt>(*stmt);
  copy->var_decl_type = DataType{};
  copy->var_decl_type.kind = DataTypeKind::kNamed;
  copy->var_decl_type.type_name = cls->name;
  return copy;
}

// §8.25: a type parameter of a parameterized class stands for the type the
// specialization binds it to throughout the class, so `T x;` in a method of
// `C #(byte)` declares a byte. The local was sized by the name through the
// type tables, which hold the declaration's default, and `x = 8'hFF` read 255.
// A declaration naming a type parameter of the running class, with no packed
// dimension of its own, is taken as one of the type RunningTypeActual gives.
// Any other declaration is returned as it is.
static const Stmt* DeclOfTypeParam(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const DataType& type = stmt->var_decl_type;
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      type.packed_dim_left != nullptr || !type.type_params.empty()) {
    return stmt;
  }
  const DataType* actual = RunningTypeActual(type.type_name, ctx);
  if (actual == nullptr || actual->kind == DataTypeKind::kImplicit) return stmt;
  auto* copy = arena.Create<Stmt>(*stmt);
  copy->var_decl_type = *actual;
  copy->var_decl_type.param_arg_name = {};
  return copy;
}

void ExecFuncVarDecl(const Stmt* stmt, StaticFrame frame, SimContext& ctx,
                     Arena& arena) {
  stmt = DeclOfThisTypeRef(stmt, ctx, arena);
  stmt = DeclOfTypeParam(stmt, ctx, arena);
  stmt = DeclShapedByTypedef(stmt, ctx, arena);
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, ctx, arena);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, frame.name, ctx, arena);
    return;
  }
  // §13.4.2: a static subroutine's frame is pushed holding the variables the
  // last call left (SimContext::PushStaticScope), so its local is found here
  // and its aggregate is referred to again. §6.21 with §6.8: an automatic
  // subroutine's local is created, and its initializer run, on every entry
  // to the block declaring it, so a loop body's `int j = 0;` starts at 0 on
  // each iteration; found and kept, it held the last iteration's j.
  if (frame.is_static_sub && ctx.FindLocalVariable(stmt->var_name)) {
    RestoreStaticAggregate(frame.name, stmt->var_name, ctx);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               CarrierInit(stmt), ctx, arena);
  CreateFuncLocalAggregate(stmt, v, ctx, arena);
  if (frame.is_static_sub)
    RetainStaticAggregate(frame.name, stmt->var_name, ctx, arena);
}

}  // namespace delta
