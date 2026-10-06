#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
// §37.59's vpiRefObj -- the reference an expression naming a variable is --
// and §37.29's vpiVirtualInterfaceVar are defined in the SystemVerilog VPI
// header.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// The object a system task or function call stands as while a PLI application
// runs for it (§37.42), with the arguments the call site wrote (§36.4), and
// the systf object a call reaches, which the procedure walk finds too.

namespace delta {

namespace {

// §37.59 with §37.58: the kind of expr an actual naming no variable is: a call
// of a function a func call, of a system function a sys func call, a literal
// a constant, and any other expression the operation its operator makes.
int RunTimeArgumentKind(const Expr& actual) {
  switch (actual.kind) {
    case ExprKind::kCall:
      return vpiFuncCall;
    case ExprKind::kSystemCall:
      return vpiSysFuncCall;
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
      return vpiConstant;
    default:
      return vpiOperation;
  }
}

// §37.58: the vpiConstType of a constant the literal `actual` is.
int RunTimeConstType(const Expr& actual) {
  if (actual.kind == ExprKind::kRealLiteral) return vpiRealConst;
  if (actual.kind == ExprKind::kStringLiteral) return vpiStringConst;
  return vpiIntConst;
}

// §36.4: one task/function argument as the application reaches it. An actual
// that names a variable is carried by that variable itself, so a write through
// vpi_put_value lands where the design will read it and a read sees whatever
// the design last wrote -- the clause asks for both, "PLI routines are provided
// that allow the PLI applications to read and write to the task/function
// arguments". Anything else is an expression rather than a name: its value goes
// into a holder of its own, which reads correctly and which a write cannot
// carry back to a call site with nowhere to put it.
//
// §37.42 detail 8 spells an omitted argument, which a call site writes as an
// empty position, and VpiMakeEmptyArgument is what sets that shape.
//
// `evaluate` is what separates the two periods a call object is built in.
// §36.8.3 has the calltf called "each time the associated user-defined system
// task or system function is executed", so an actual that is an expression has
// a value there and the holder is filled with it. §36.8.2 has the compiletf
// called "when the user-defined system task or system function name is
// encountered during parsing or compiling", where the design has not run: there
// is no value to read, and reading one would mean running the source's own
// functions once per call site before the simulation started, so the holder is
// left empty and the argument stands for what the source wrote rather than for
// what it will produce.
VpiObject* SystfCallArgument(VpiObject* arg, const Expr* actual,
                             SimContext& ctx, Arena& arena, bool evaluate) {
  if (actual == nullptr) {
    VpiMakeEmptyArgument(arg);
    return arg;
  }
  Variable* named = actual->kind == ExprKind::kIdentifier
                        ? ctx.FindVariable(actual->text)
                        : nullptr;
  if (named != nullptr) {
    arg->type = vpiRefObj;
    // Expr::text is a view into the source buffer, which does not end where the
    // identifier does, so the name is copied into the run's arena to be the
    // standalone string VpiObject::name has to hold. Without the copy
    // vpi_get_str(vpiName, arg) reported the rest of the source file.
    arg->name = std::string_view(
        arena.AllocString(actual->text.data(), actual->text.size()),
        actual->text.size());
    arg->var = named;
  } else {
    arg->type = RunTimeArgumentKind(*actual);
    if (arg->type == vpiConstant) arg->const_type = RunTimeConstType(*actual);
    auto* holder = arena.Create<Variable>();
    if (evaluate) holder->value = EvalExpr(actual, ctx, arena);
    arg->var = holder;
  }
  // §37.3.5: an application reaches the source's expressions, however complex,
  // either as arguments of system tasks and functions (§36.4) or by walking the
  // design hierarchy, and evaluating one can have side effects. This is that
  // first way, and
  // VpiObject::has_side_effects is the mark the value, property and relation
  // routines settle the subclause's rules by. No pass wrote it, so no argument
  // an application was ever handed was an expression with side effects and
  // every one of those rules stood over an empty set.
  arg->has_side_effects = VpiSourceExprHasSideEffects(actual);
  arg->size = static_cast<int>(arg->var->value.width);
  return arg;
}

// §37.61 detail 1: vpiPrefix is non-NULL for an object standing for a source
// expression or task call that a virtual interface or a clocking block
// prefixes. A system task or
// function argument written `vif.sig` is such an expression and `vif` is the
// virtual interface var prefixing it, so this answers that variable and
// nullptr for an actual written any other way. It is what decides whether the
// argument object is built as a dynamically prefixed one at all: nothing in the
// run ever wrote VpiObject::prefix, so vpi_handle(vpiPrefix, arg) reported NULL
// for every object any design produced and the whole subclause stood over
// objects a test had built by hand.
Variable* DynamicPrefixBaseVar(const Expr* actual, SimContext& ctx) {
  if (actual == nullptr || actual->kind != ExprKind::kMemberAccess) {
    return nullptr;
  }
  if (actual->lhs == nullptr || actual->lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  Variable* base = ctx.FindVariable(actual->lhs->text);
  return ctx.IsVirtualInterfaceVar(base) ? base : nullptr;
}

// §25.9: the interface member a prefixed argument names, which is the right
// side of the member access when that is a plain name and the access's own text
// otherwise -- the shape the expression evaluator reads such a reference in.
std::string_view DynamicPrefixFieldName(const Expr* actual) {
  return (actual->rhs != nullptr && actual->rhs->kind == ExprKind::kIdentifier)
             ? actual->rhs->text
             : actual->text;
}

// §37.61: what a dynamically prefixed argument is made from. `base` is the
// virtual interface var the source wrote as the prefix; `member` is the
// interface instance's variable the named member resolves to; `actual` is the
// instance the prefix holds at the current simulation time, which §37.61 detail
// 3 reads as whether the prefix has a corresponding actual. The last two are
// null exactly while the virtual interface holds null.
struct DynamicPrefix {
  Variable* base = nullptr;
  Variable* member = nullptr;
  VpiHandle actual = nullptr;
};

// §25.9: resolve the prefix against the run. An unbound virtual interface
// denotes no instance, so it reaches neither a member variable nor an actual.
DynamicPrefix ResolveDynamicPrefix(const Expr* actual, Variable* base,
                                   SimContext& ctx, VpiContext& vpi) {
  DynamicPrefix prefix;
  prefix.base = base;
  if (!ctx.VirtualInterfaceIsBound(base)) return prefix;
  std::string scope(ctx.VirtualInterfaceBinding(base));
  prefix.member = ctx.FindVariable(scope + "." +
                                   std::string(DynamicPrefixFieldName(actual)));
  prefix.actual = vpi.HandleByName(scope.c_str(), nullptr);
  return prefix;
}

// The run's arena is where a string a VpiObject holds has to live: Expr::text
// is a view into the source buffer, which does not end where the name does, and
// a joined name is a temporary that the object would outlive.
std::string_view ArenaName(Arena& arena, const std::string& name) {
  return std::string_view(arena.AllocString(name.data(), name.size()),
                          name.size());
}

// §37.61 (figure): fill `arg` as the dynamically prefixed object the actual
// stands for and `prefix` as the object it is prefixed by. The figure draws the
// vpiPrefix arrow from a simple expression -- §37.58's reference -- to the
// virtual interface var, and gives the prefixed object the "-> has actual"
// property that detail 3 answers off the prefix.
void FillPrefixedArgument(VpiObject* arg, VpiObject* prefix, const Expr* actual,
                          const DynamicPrefix& resolved, Arena& arena) {
  prefix->type = vpiVirtualInterfaceVar;
  prefix->name = ArenaName(arena, std::string(actual->lhs->text));
  prefix->var = resolved.base;
  // §37.29 (figure, Example 2): vpiActual of a virtual interface var is the
  // interface instance it holds, and NULL while it holds none.
  prefix->actual = resolved.actual;

  arg->type = vpiRefObj;
  arg->name = ArenaName(arena, std::string(actual->lhs->text) + "." +
                                   std::string(DynamicPrefixFieldName(actual)));
  arg->prefix = prefix;
  // §36.4: an actual that names a variable is carried by that variable itself,
  // so an application reads and writes the interface instance's own storage. An
  // unbound prefix names none, and a holder of its own stands where it would.
  arg->var =
      resolved.member != nullptr ? resolved.member : arena.Create<Variable>();
  arg->size = static_cast<int>(arg->var->value.width);
}

// What one invocation's arguments are built with: the context whose objects
// they are and that an argument's prefix is resolved against, the run whose
// variables they name, where their values live, whether their values are read
// yet, and where an object is allocated.
struct SystfArgumentBuild {
  VpiContext& vpi;
  SimContext& ctx;
  Arena& arena;
  bool evaluate;
  std::function<VpiObject*()> alloc;
};

// §36.4: the arguments the call site wrote, held as the call's arguments so
// §37.42's vpiArgument iteration reaches them.
void AppendSystfCallArguments(VpiObject* call, const Expr& call_site,
                              const SystfArgumentBuild& build) {
  for (const Expr* actual : call_site.args) {
    VpiObject* arg = build.alloc();
    // §37.61 detail 1: an actual the source prefixed by a virtual interface
    // is the prefixed object the clause is written about, and it is built as
    // one rather than as the anonymous expression holder every non-identifier
    // actual used to become.
    Variable* base = DynamicPrefixBaseVar(actual, build.ctx);
    if (base != nullptr) {
      FillPrefixedArgument(
          arg, build.alloc(), actual,
          ResolveDynamicPrefix(actual, base, build.ctx, build.vpi),
          build.arena);
    } else {
      SystfCallArgument(arg, actual, build.ctx, build.arena, build.evaluate);
    }
    call->arguments.push_back(arg);
  }
}

// §37.42 detail 3: the model's object for the call statement `call_site`,
// written in the instance `prefix` names, or in any instance writing it where
// `prefix` names none of them; null where the model holds no statement making
// the call. A run names an instance with a dot after it and the model without.
VpiObject* CallSiteObject(const VpiCallSiteObjects& sites,
                          const Expr* call_site, std::string prefix) {
  if (call_site == nullptr) return nullptr;
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  auto exact = sites.find({call_site, prefix});
  if (exact != sites.end()) return exact->second;
  auto first = sites.lower_bound({call_site, std::string()});
  if (first != sites.end() && first->first.first == call_site) {
    return first->second;
  }
  return nullptr;
}

// The position of the registration `data` among `systfs`, -1 for a record
// that is none of them.
int RegistrationIndex(const std::vector<s_vpi_systf_data>& systfs,
                      const s_vpi_systf_data& data) {
  for (std::size_t i = 0; i < systfs.size(); ++i) {
    if (&systfs[i] == &data) return static_cast<int>(i);
  }
  return -1;
}

}  // namespace

VpiObject* VpiSystfObjectAt(const std::vector<VpiObject*>& objects, int index) {
  for (VpiObject* obj : objects) {
    if (obj->is_systf && obj->index == index) return obj;
  }
  return nullptr;
}

// §37.42: the object standing for one system task or system function call,
// carrying the arguments the call site wrote and, where the registration is a
// system function, the storage its return value is written through. Both
// periods that call a PLI application build one, and `evaluate_args` is the
// whole of the difference between them: an execution-time call reads each
// actual's value, a build-period call has none to read.
VpiHandle VpiContext::MakeSystfCallObject(const s_vpi_systf_data& data,
                                          const Expr* call_site,
                                          SimContext& ctx, Arena& arena,
                                          bool evaluate_args) {
  // §37.42 detail 3: the system task or function call a PLI application is run
  // for, which the application reaches with vpi_handle(vpiSysTfCall, NULL).
  // Where the model holds the statement making the call, the call is that
  // object, so the handle the application is given and the one it reaches by
  // walking the design are one object under §38.3; a call the model builds no
  // statement for, such as one written in a task's body, stands up an object
  // of its own. Each invocation hangs its own arguments and value storage on
  // the call.
  VpiObject* call =
      CallSiteObject(call_site_objects_, call_site, ctx.ActiveInstancePrefix());
  if (call == nullptr) {
    call = AllocObject();
    call->name = data.tfname != nullptr ? std::string_view(data.tfname)
                                        : std::string_view();
    // §37.3.3: the call stands for the text its call site was written as.
    if (call_site != nullptr) {
      VpiRecordWrittenLocation(call, call_site->range.start, ctx);
    }
  }
  call->type = (data.type == vpiSysFunc) ? vpiSysFuncCall : vpiSysTaskCall;
  // §37.42 detail 9: the call decompiles to the one the source wrote.
  if (call_site != nullptr) call->decompile = VpiExprDecompile(call_site);
  // §37.42 detail 5: every call built here is of a registration an
  // application made, so it is user-defined, and the figure's arrow reaches
  // the systf object that registration returned.
  call->user_defined = true;
  call->user_systf =
      VpiSystfObjectAt(all_objects_, RegistrationIndex(systfs_, data));
  call->arguments.clear();

  // It is also where a system function's return value is put: vpi_put_value
  // writes through the object's own storage, so the call carries a variable
  // of its own for the application to write and for this routine's caller to
  // read back.
  auto* value_holder = arena.Create<Variable>();
  // §36.8.1: "The value returned by the sizetf routine shall be the number of
  // bits that the calltf routine shall provide as the return value for the
  // system function", so the holder the application writes through is that
  // wide. §38.37.1's default is what SystfResultSizeBits answers where no
  // sizetf is provided: "a user-defined system function of type vpiSizedFunc or
  // vpiSizedSignedFunc shall return 32 bits". A sizetf answering with no bits
  // at all describes no value, so the default stands rather than a width
  // nothing can hold.
  int result_bits = SystfResultSizeBits(data);
  auto width = static_cast<uint32_t>(
      result_bits > 0 ? result_bits : kVpiDefaultSizedFuncBits);
  value_holder->value = MakeLogic4VecVal(arena, width, 0);
  call->var = value_holder;
  call->size = static_cast<int>(width);

  // §36.4: the arguments the call site wrote. They are attached before the
  // routine runs, because the application reads them from inside it.
  if (call_site != nullptr) {
    AppendSystfCallArguments(
        call, *call_site,
        SystfArgumentBuild{*this, ctx, arena, evaluate_args,
                           [this] { return AllocObject(); }});
  }
  return call;
}

}  // namespace delta
