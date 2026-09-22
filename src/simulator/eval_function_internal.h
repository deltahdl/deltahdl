#pragma once

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct DataType;
struct Expr;
struct FunctionArg;
struct ModuleItem;
struct Stmt;
class SimContext;
class Arena;

// §6.11.2 names the 4-state types -- logic, reg, integer and time -- and says
// "the other types do not have unknown values", which decides whether an
// unknown assigned to an object declared with this type is converted to zeros.
// Defined in eval_function_body.cpp and asked by every site that creates one of
// a subroutine's variables: its declared locals, its formal arguments and the
// implicit variable holding its return value.
//
// A type reached through a name answers 4-state. Is4stateType is asked of the
// kind alone and a DataTypeKind::kNamed answers false whatever the name stands
// for, so answering from it would convert the unknowns of a `typedef logic`
// object. Keeping a bit §6.11.2 would have cleared is the smaller error than
// clearing one it would have kept, and #3486 is what would carry a name's
// resolved kind this far.
bool DeclaredTypeIs4State(const DataType& type);

// §13.3 and §13.4 with §6.8: executes the variable declaration `stmt` of the
// body of a subroutine -- the local's storage, kinds, default and
// initializer, kept across calls for a static one (§13.4.2) under
// `static_frame`, the key the subroutine's static locals are kept under:
// the subroutine's name, qualified by the class level declaring it for a
// method (StaticLocalFrame in eval_function_body.cpp). Defined in
// eval_function_body_decl.cpp; called by the statement executor in
// eval_function_body.cpp.
void ExecFuncVarDecl(const Stmt* stmt, std::string_view static_frame,
                     SimContext& ctx, Arena& arena);

// §6.18 with §7.2.1: binds the variable `var_name` to the layout its typedef
// name `type` stands for, where the name is a registered structure or union
// (RegisterDesignTypeLayouts), so a member read or write of it is a window of
// that layout. Answers whether a layout was bound. Defined in
// eval_function_body_decl.cpp; also used for the subroutine's implicit
// variable by BindReturnStructLayout in eval_function_body.cpp.
bool BindNamedLayout(std::string_view var_name, const DataType& type,
                     SimContext& ctx);

// §10.4's blocking assignment as a subroutine body performs it, over every
// left-hand side that body admits: an identifier, a select, `this.f`,
// `super.f`, an unqualified property of the enclosing object, and the member of
// whatever an ordinary handle denotes. Defined in
// eval_function_body_assign.cpp and called by the statement executor in
// eval_function_body.cpp, which holds the declaration and control-flow forms.
void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
// §8.11: writes `val` to the property the bare identifier `lhs` names
// inside a method -- a static property of the class the method belongs to,
// or the instance property of the object it was invoked on -- and answers
// whether it did; false outside a method, where no object is in scope. It
// is asked for a name no local answers, a local being the name's own
// declaration (eval_function_body_assign.cpp).
bool TryFuncClassPropertyWrite(const Expr* lhs, const Logic4Vec& val,
                               SimContext& ctx, Arena& arena);

// Shared between eval_system_task.cpp and eval_system_func.cpp. The system-task
// helpers are defined once in eval_system_task.cpp; the system-function
// dispatch in eval_system_func.cpp routes to them.
// §20.14: the three probabilistic functions EvalPrngCall answers for. It is
// asked before that function is called rather than after, so that a name it
// does not match reaches the end of the dispatch chain instead of being given
// a value by the last matcher tried.
bool IsPrngSysCall(std::string_view name);
Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name);
bool IsDisplayOrWriteTask(std::string_view name);
void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena);
void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os);
Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena);
bool IsStrobeTask(std::string_view name);
bool IsMonitorTask(std::string_view name);
Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena, std::string_view name);
bool IsVcdSysCall(std::string_view name);
Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name);

// Shared with eval_function.cpp, whose call-dispatch entry points invoke them.
// The subroutine argument-binding helpers are defined in
// eval_function_args.cpp; ExecFunctionBody and the statement executor it drives
// are defined in eval_function_body.cpp.
struct Variable;
struct ClassObject;
void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);
// §13.5.4: the position in the call's argument list of the actual bound to the
// formal at `param_idx` -- its own position while the actuals are positional,
// the position of the one named after it once they are named -- or -1 where
// the call supplies none, so the formal takes its default. Defined in
// eval_function_args.cpp; the copy-out on return in
// eval_function_args_writeback.cpp asks it for the same pairing.
int ResolveArgIndex(const ModuleItem* func, const Expr* expr, size_t param_idx);
// §10.9.2 with §13.5.1: an assignment pattern as the actual of a structure
// formal, and §11.9: a tagged union expression as the actual of a tagged-union
// formal. TryEvalPatternActual evaluates a bare or typed pattern against the
// formal's layout, and a tagged expression whose member value is a pattern
// against the layout of the member it names within the formal's union,
// answering false where the actual has another shape, so it is evaluated as
// any expression; TryBindTaggedActual binds the union's layout and the
// member's tag to the formal, answering false where the actual is no tagged
// expression or the formal's type has no layout. §13.5.1:
// TryBindInlineAggregateFormal binds the layout of a formal whose structure
// or union is written inline in its declaration, tagged or not, whatever the
// actual is, answering false where the formal's type writes no members; the
// layout is built once from the declaration's type and keyed by it.
// TryBindNamedAggregateFormal binds the layout registered under the typedef
// name a formal is declared by, answering false where the name has none. All
// four are defined in eval_function_args_tagged.cpp and asked by the by-value
// binding in eval_function_args.cpp.
bool TryEvalPatternActual(const FunctionArg& param, const Expr* actual,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryBindTaggedActual(const FunctionArg& param, const Expr* actual,
                         SimContext& ctx);
bool TryBindInlineAggregateFormal(const FunctionArg& param, SimContext& ctx);
bool TryBindNamedAggregateFormal(const FunctionArg& param, SimContext& ctx);
// §13.3 with §10.7: the declared width of a by-value formal of type `dt`, the
// one BindValueArg resizes the actual's value into, or zero for a type no
// width applies to -- a class handle. Defined in eval_function_args_tagged.cpp.
uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx, Arena& arena);

// The actual arguments of one call, as §35.6.1 "Argument passing" and §11.12
// "Let construct" each describe them: the call-site expression, the boundary
// between the positional actuals and the named ones, and the environment the
// actuals are evaluated in. It is declared here rather than in either caller
// because both take it -- the DPI import binding in eval_function_dpi.cpp and
// the let-construct binding in eval_let.cpp.
struct ActualBindingCtx {
  const Expr* call;
  size_t positional_count;
  SimContext& ctx;
  Arena& arena;
};

// §35.6: a call to an imported subroutine, evaluated against the DpiRuntime
// SimContext holds. It is the fallback of EvalFunctionCall in
// eval_function.cpp, which reaches it once no native subroutine of that name is
// found; the body is in eval_function_dpi.cpp, where the conversion between the
// evaluator's Logic4Vec and the DpiArgValue the registry speaks lives.
Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena);

struct ClassTypeInfo;
struct MethodCallParts;

// The object and method a call through a handle names, `h.m(...)`, with the
// class the method is defined in, so its body resolves unqualified members
// against that level (§8.15 member shadowing across a base/derived hierarchy).
// Resolved by ResolveInstanceMethod, defined in eval_function.cpp, which
// answers false when the variable holds no object or the object has no such
// method; shared with eval_instance_task.cpp, which runs a task so named as a
// coroutine.
// §8.25: the actual the `#(...)` list `actuals` gives the parameter `pname`,
// the i-th of the class's: by name where an actual was written `.name(type)`
// (§23.10.2.2), else by position, and null where the list gives it none, which
// leaves the parameter at the default the class declares. Defined in
// eval_class_params.cpp; shared with the construction of a base level in
// eval_class_new.cpp, whose extends clause is such a list.
const DataType* ActualForParam(const std::vector<DataType>& actuals, size_t i,
                               std::string_view pname);

struct InstanceMethodInfo {
  ClassObject* obj = nullptr;
  ModuleItem* method = nullptr;
  const ClassTypeInfo* owner = nullptr;
};
bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                           InstanceMethodInfo& info);
// The method `method_name` called on `obj` through a handle whose declared
// class is `declared_class`, the way ResolveInstanceMethod resolves one named
// through a variable: §8.20 dispatches a method the declared class sees as
// virtual by the object and one it holds non-virtually by the declared class,
// and §8.26.9 resolves an interface-class handle by the object. Shared with
// the containers of handles (eval_assoc_class_handles.h), whose element has no
// variable to name it by. False for a null `obj` or a method the object's
// class does not have. Defined in eval_function.cpp.
bool ResolveMethodByDeclaredClass(ClassObject* obj,
                                  std::string_view declared_class,
                                  std::string_view method_name, SimContext& ctx,
                                  InstanceMethodInfo& info);
// Runs the method ResolveInstanceMethod answered, `expr` the call whose
// actuals bind its formals: a static method in class scope (§8.10), an
// instance method on the object with the method's defining class as the
// enclosing scope (§8.15). Defined in eval_function.cpp; shared with
// eval_instance_task.cpp, which runs a method a statement names without the
// parentheses (§13.5.5).
Logic4Vec RunInstanceMethod(const InstanceMethodInfo& info, const Expr* expr,
                            SimContext& ctx, Arena& arena);

// §8.23 has the left operand of `::` name a class or a package, and §26.3
// reaches a package's class through `p::C`, so the operand of `p::C::m` is
// itself a scope resolution of two identifiers. Answers the key under which
// SimContext holds the class for either shape, or an empty view for another.
// Defined in eval_function.cpp; shared with eval_instance_task.cpp, which
// resolves a static task named through the class scope.
std::string_view ScopedClassKey(const Expr* scope, Arena& arena);

// §26.3 with §8.6: a method is called through a handle by the syntax a
// property is read by, and the handle may be a package's variable named
// through the package scope resolution operator, `p1::h.m(...)`, which the
// parser leaves as a scope resolution of two identifiers on the handle side
// of the member access. The variable is held under the "p1.h" key a scoped
// read resolves by (BuildMemberName in eval_expr.cpp), and its class is
// recorded under the same key (RegisterPackageClassVariables in
// lowerer_package_class_vars.cpp), so the receiver is that key, given the
// arena's lifetime as ScopedClassKey gives a class key. Answers what
// ExtractMethodCallParts answers for an identifier receiver, that key for a
// scoped one, and false for any other shape. Defined in
// eval_instance_task.cpp; shared with eval_function.cpp, which dispatches the
// call expression, where the statement form is resolved beside it, and with
// every built-in method's receiver -- the process, semaphore, array, queue
// and randomize paths -- which took an identifier alone.
bool ExtractHandleMethodCallParts(const Expr* expr, Arena& arena,
                                  MethodCallParts& out);

// §8.6 (printed page 183): the call `expr`, `<base>.m(...)`, run on the
// object its base evaluates to where the base is a chained property
// receiver -- `c.kid.m()`, `arr[0].kid.m()`, a static property named through
// the class scope -- the method resolved by the object's own class. A base
// that is a bare name, an element of a container, or a path starting at a
// call is left to the arms that know its declared class or own its
// evaluation (TryEvalClassMethodCall, the element arms,
// TryEvalCallResultMethodCall), so this is asked after them and evaluates
// the base once -- but for a bare name that is a static property of the
// running method's class (§8.9), which the shared resolver takes by the
// property's declared class (ResolveMethodOnStaticHandle), no `this` being
// in force for the arms to read it through. Defined in eval_instance_task.cpp
// beside the statement form's resolver, which it shares; before it, `y =
// c.kid.get()` reached no arm of TryDispatchMethodOrLet and read 0.
bool TryEvalMethodOnEvaluatedBase(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out);

// The same for the member access `access` itself, `h.m` or `p1::h.m`, the
// receiver of a call and the parenthesis-free statement §13.5.5 allows, a
// reduction or locator written without its parentheses (§7.12), and the
// `h.x` a named rand_mode() or constraint_mode() call is made on (§18.8,
// §18.9). `var_name` is the handle's key and `method_name` the member.
bool ExtractHandleAccessParts(const Expr* access, Arena& arena,
                              MethodCallParts& out);

// §8.7/§8.15: whether `call`, a `super.new(...)` call, is one the construction
// of the object has already made -- the first statement of the constructor of
// the class whose method is running, or §8.17's `super.new(default)`.
// EvalClassNew, in eval_class_new.cpp, calls the base class constructor with
// that statement's arguments before the body runs, so the statement itself
// runs nothing when the body reaches it; the `super` dispatch in
// eval_function.cpp asks here.
bool IsSuperNewRunByConstruction(const Expr* call, SimContext& ctx);

// Runs a resolved class method on a concrete object (sets `this`, binds args,
// writes back). Defined in eval_function.cpp; reused by eval_randomize.cpp to
// invoke pre_randomize()/post_randomize() on the randomized object.
Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena);

// 8.10: target of a class-method invocation -- the method plus, for a
// parameterized class, its bound type so the return width resolves. Shared so
// the static-method dispatch in eval_static_method.cpp can run a method body
// without a `this`. Defined (the body) in eval_function.cpp.
struct ClassMethodTarget {
  ModuleItem* method = nullptr;
  const ClassTypeInfo* param_cls = nullptr;
};
void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out);

// 8.10/8.9: a static-method call has no `this`, so it runs in class scope
// (target.param_cls is the scope class) and unqualified static-member access
// targets the single shared slot. Defined in eval_static_method.cpp.
// RunStaticMethodInClassScope is the shared runner (instance-handle path);
// TryEvalEnclosingStaticCall handles an unqualified call inside a static
// method.
void RunStaticMethodInClassScope(ClassMethodTarget target, const Expr* expr,
                                 SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

// 8.13/8.6: a subclass inherits the members of its base class, methods among
// them, so a call with no receiver inside a class method names a method of the
// enclosing class or of one it inherits from, run on the object the enclosing
// method is running on. Returns false when the call is qualified, when there is
// no enclosing method object, or when no such method exists, so module-level
// lookup proceeds. Defined in eval_static_method.cpp beside the static form.
bool TryEvalEnclosingInstanceCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out);

// 18.6/8.26.9: handle a built-in randomize() method call on a class handle
// (including an interface-class handle). Returns false when the call is not a
// randomize() on a resolvable class object, so normal method dispatch proceeds.
// Defined in eval_randomize.cpp.
bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

// §18.12: handle a scope randomize call, std::randomize(...) or its bare
// randomize(...) spelling used outside a class method. The named arguments are
// the variables of the current scope to be assigned random values; the call
// returns 1 when it sets them all to valid values and 0 otherwise, and the
// no-argument form is a checker that changes nothing. Returns false when the
// call is not a serviceable scope randomize, so normal method/function dispatch
// proceeds. Defined in eval_randomize.cpp.
bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

// §18.13.3: handle a built-in srandom(int seed) method call on a class handle,
// seeding that object's RNG. Returns false when the call is not an srandom() on
// a resolvable class object, so normal method dispatch proceeds. Defined in
// eval_randomize.cpp.
bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out);

// §18.13.4/§18.13.5: handle built-in get_randstate()/set_randstate() method
// calls on a class handle, retrieving or installing that object's RNG state.
// Each returns false when the call is not the matching form on a resolvable
// class object, so normal method dispatch proceeds. Defined in
// eval_randomize.cpp.
bool TryEvalObjectGetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);
bool TryEvalObjectSetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

// §18.9: handle a built-in constraint_mode() method call on a class handle,
// setting a constraint block active/inactive (void form) or returning its
// current active state (nonvoid form). Returns false when the call is not a
// constraint_mode() on a resolvable class object, so normal method dispatch
// proceeds. Defined in eval_randomize.cpp.
bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

// §18.8: handle a built-in rand_mode() method call on a class handle, setting a
// random variable active/inactive (void form) or returning its current active
// state (nonvoid form). A void call that names no variable applies to every
// random variable in the object. Returns false when the call is not a
// rand_mode() on a resolvable class object, so normal method dispatch proceeds.
// Defined in eval_randomize.cpp.
bool TryEvalObjectRandMode(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena);
// §13.4.1 with §6.16: marks a string-returning function's implicit variable
// as the string its return type declares, with no width. Defined in
// eval_function_body_assign.cpp; ExecFunctionBody asks it as the body starts.
void ShapeStringReturnVariable(const ModuleItem* func, Variable* ret_var,
                               SimContext& ctx, Arena& arena);
// §13.4.1 with §8.7: records a class-returning function's implicit variable
// as a handle of its return type, so that `f = new` and `return new` construct
// it. Both defined in eval_function_body_assign.cpp; ExecFunctionBody asks
// the first as the body starts, ExecFuncReturn the second for a `new`.
void ShapeClassReturnVariable(const ModuleItem* func, Variable* ret_var,
                              SimContext& ctx, Arena& arena);
bool TryFuncReturnClassNew(Expr* returned, std::string_view func_name,
                           SimContext& ctx, Arena& arena);
void WritebackQueueRefs(SimContext& ctx);
void WritebackAssocRefs(SimContext& ctx);

// §9.7 built-in process control. The handlers live in eval_process_methods.cpp;
// the call dispatch in eval_function.cpp routes to them.
// TryEvalProcessStaticCall handles `process::self()`; TryEvalProcessMethodCall
// handles p.status()/kill()/suspend()/resume()/srandom()/get_randstate()/
// set_randstate(). Each returns false
// when the call is not the matching process form, so normal dispatch proceeds.
bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);
bool TryEvalProcessMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

// §15.5.3: routes the parenthesized call form of the named-event triggered
// method (ev.triggered()) to the same triggered-state evaluation used for the
// bare-member form. Returns false when the call is not a triggered() invocation
// on a named event, so normal method dispatch proceeds. Defined in
// eval_expr.cpp alongside the member-access triggered handler.
bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

}  // namespace delta
